import Langlands.Representation.Plancherel.RationalUnitaryPoleFactorization
import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation

/-! # Unitary cancellation with two denominators for the same operator -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel.RationalUnitaryPoleFactorization

open UnramifiedOperatorFamily

universe u uV uW uE

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hG : IsConnectedReductive G)

local instance denominatorCancellationPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

set_option hygiene false in
set_option quotPrecheck false in
local notation "X" => unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)
set_option hygiene false in
set_option quotPrecheck false in
local notation "Xu" => unitaryUnramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {D : Set (unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul))}
  {J : D → V →ₗ[ℂ] W}

/-- Cancel the unitary poles of a second quotient representing the same
operator. Its denominator may vanish on the original domain; agreement
after cancellation holds at every point where the remainder is nonzero. -/
def cancelFromCross
    (p : RationalOperatorContinuationData D J) (e : W ≃ₗ[ℂ] E)
    (b : unramifiedRegularFunctions (fun a => (rationalNormCharacters G a).toMul))
    (f : RationalUnitaryPoleFactorization G b)
    (N : X → V →ₗ[ℂ] W)
    (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
    (hcross : ∀ z, p.denominator.val z • N z = b.val z • p.numerator z)
    (hD : Dense (unitaryToUnramified G ⁻¹' D))
    (hbound : ∀ v : V, ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Xu) (hz : unitaryToUnramified G z ∈ D),
      ‖e (J ⟨unitaryToUnramified G z, hz⟩ v)‖ ≤ C) :
    RationalOperatorContinuationData (D ∩ {z : X | f.remainder.val z ≠ 0})
      (fun z => J ⟨z.val, z.property.1⟩) := by
  let s := rationalUnitaryPoleProduct G f.poles
  have hNclear (z : D) : N z.val = b.val z.val • J z := by
    apply smul_right_injective (V →ₗ[ℂ] W) (p.denominator_nonzero z)
    calc
      p.denominator.val z.val • N z.val = b.val z.val • p.numerator z.val := hcross z.val
      _ = p.denominator.val z.val • (b.val z.val • J z) := by
        rw [p.clears z, smul_smul, smul_smul, mul_comm]
  have hNbound : HasClearedUnitaryBound G (fun z => e.toLinearMap.comp (N z)) (s * f.remainder) := by
    rw [← f.factorization]
    apply hasClearedUnitaryBound_of_dense G _ (hN.postcomp e.toLinearMap) b _ hD
    intro v
    obtain ⟨C, hC, hCz⟩ := hbound v
    refine ⟨C, hC, fun z hz => ?_⟩
    let w := unitaryToUnramified G z
    change ‖e (N w v)‖ ≤ C * ‖b.val w‖
    calc
      ‖e (N w v)‖ = ‖b.val w‖ * ‖e (J ⟨w, hz⟩ v)‖ := by
        rw [hNclear ⟨w, hz⟩, LinearMap.smul_apply, map_smul, norm_smul]
      _ ≤ ‖b.val w‖ * C := mul_le_mul_of_nonneg_left (hCz z hz) (norm_nonneg _)
      _ = C * ‖b.val w‖ := mul_comm _ _
  let Q := rationalUnitaryCancelledModelOperator G hG f.poles N hN e f.remainder hNbound
  have hQ : IsPolynomialOperatorOn Set.univ (fun z => Q z.val) :=
    rationalUnitaryCancelledModelOperator_isPolynomial G hG f.poles N hN e f.remainder hNbound
  have hQspec (z : X) : N z = s.val z • Q z :=
    rationalUnitaryCancelledModelOperator_spec G hG f.poles N hN e f.remainder hNbound z
  have hs : s ≠ 0 := by
    let := rationalUnramifiedRegularFunctions_isDomain G
      (continuous_rationalValuationImageProjection G) hG
    apply List.prod_ne_zero
    intro hm
    obtain ⟨r, _, hr⟩ := List.mem_map.mp hm
    exact r.factor_ne_zero G hG hr
  have hds : Dense {z : X | s.val z ≠ 0} := rationalUnramifiedRegular_dense_nonzero G
    (continuous_rationalValuationImageProjection G) hG s hs
  have hc (z : X) (hz : s.val z ≠ 0) :
      p.denominator.val z • Q z = f.remainder.val z • p.numerator z := by
    have he := hcross z
    rw [hQspec z, f.factorization] at he
    change p.denominator.val z • (s.val z • Q z) =
      (s.val z * f.remainder.val z) • p.numerator z at he
    rw [smul_smul, mul_comm (p.denominator.val z), mul_smul, mul_smul] at he
    exact smul_right_injective (V →ₗ[ℂ] W) hz he
  have hc_all (z : X) : p.denominator.val z • Q z = f.remainder.val z • p.numerator z := by
    apply LinearMap.ext
    intro v
    let q : X → W := fun w => p.denominator.val w • Q w v - f.remainder.val w • p.numerator w v
    have hq : IsPolynomialOn Set.univ (fun w => q w.val) :=
      ((hQ v).regular_smul p.denominator).sub ((p.polynomial v).regular_smul f.remainder)
    exact sub_eq_zero.mp (polynomial_eq_zero_on_open_of_dense hds isOpen_univ q hq
      (fun w hw _ => by
        simpa only [q, sub_eq_zero, LinearMap.smul_apply] using
          congrArg (fun T : V →ₗ[ℂ] W => T v) (hc w hw)) z (Set.mem_univ _))
  refine ⟨f.remainder, fun z => z.property.2, Q, hQ, fun z => ?_⟩
  let w : D := ⟨z.val, z.property.1⟩
  apply smul_right_injective (V →ₗ[ℂ] W) (p.denominator_nonzero w)
  calc
    p.denominator.val w.val • Q w.val = f.remainder.val w.val • p.numerator w.val := hc_all _
    _ = p.denominator.val w.val • (f.remainder.val w.val • J w) := by
      rw [p.clears w, smul_smul, smul_smul, mul_comm]

end Langlands.Plancherel.RationalUnitaryPoleFactorization

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor UnramifiedOperatorFamily

universe u uV uE

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "V₀" => compactFiber χ K ψ hψ A
local notation "V₁" => compactFiber χ K ψ' hψ' A
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q

/-- A factorization of a cross-related denominator gives actual regular germs,
even if that denominator has zeros in the original genuine generic locus. -/
theorem exists_regularGermAt_of_poleFactorization_cross
    (c : RationalOperatorContinuationData D J)
    (b : unramifiedRegularFunctions (normCharacters χ))
    (f : RationalUnitaryPoleFactorization (parameterScheme χ) b)
    (N : X → V₀ →ₗ[ℂ] V₁)
    (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
    (hcross : ∀ z, c.denominator.val z • N z = b.val z • c.numerator z)
    (hD : Dense ((unitaryParameter χ) ⁻¹' D))
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] (e : V₁ ≃ₗ[ℂ] E)
    (hbound : ∀ v : V₀, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : Xu) (hz : unitaryParameter χ z ∈ D), ‖e (J ⟨unitaryParameter χ z, hz⟩ v)‖ ≤ C)
    (z : Xu) :
    ∃ M : V₀ →ₗ[ℂ] V₁,
      RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q (unitaryParameter χ z) M := by
  let Q := f.cancelFromCross (parameterScheme χ) (parameterScheme_isConnectedReductive χ hG)
    c e b N hN hcross hD hbound
  let U : Set X := {w | f.remainder.val w ≠ 0}
  exact ⟨_, U, Q.numerator, f.remainder, f.remainder_nonzero z,
    ⟨isOpen_ne_fun (continuous_unramifiedRegularFunction _ _) continuous_const, Q.polynomial,
      fun _ hw => hw, fun w hw => Q.clears ⟨w.val, w.property, hw⟩⟩, rfl⟩

end Langlands.Plancherel.ActualCommonLeviV3
