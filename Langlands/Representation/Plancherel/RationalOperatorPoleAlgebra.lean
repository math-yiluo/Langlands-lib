import Langlands.Representation.Plancherel.RationalRankOneOperatorDenominator
import Langlands.Representation.Plancherel.CompactIntertwiningComposition

/-! # Composition and inversion of pole presentations on the actual character group -/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

universe u uV uW uZ uV' uW'

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance poleAlgebraPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

set_option hygiene false in
set_option quotPrecheck false in
local notation "ν" => fun a => (rationalNormCharacters G a).toMul
local notation "X" => unramifiedCharacters ν
local notation "R" => unramifiedRegularFunctions ν
local notation "invR" => unramifiedRegularInversion ν

namespace RationalUnitaryPoleFactorization

private theorem coordinateRoot_eval {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) ℤ (Additive (rationalDiscreteValuationImage G)))
    (a : ℂˣ) (z : X) :
    (rationalUnramifiedBasisCoordinateRoot G B a).val z =
      (rationalUnramifiedBasisUnitCoordinates G B z 0 : ℂˣ).val - a.val := by
  let c := rationalUnramifiedBasisUnitCoordinates G B z
  have h := rationalUnramifiedBasisLaurentEquiv_eval G B c (finiteLaurentCoordinateRoot n a)
  change (rationalUnramifiedBasisCoordinateRoot G B a).val
    ((rationalUnramifiedBasisUnitCoordinates G B).symm c) = _ at h
  rw [show (rationalUnramifiedBasisUnitCoordinates G B).symm c = z from
    (rationalUnramifiedBasisUnitCoordinates G B).symm_apply_apply z] at h
  rw [h, ← Fin.cons_self_tail c, finiteLaurentCoordinateRoot_eval_cons]

variable (hG : IsConnectedReductive G)

private def inversionFactor (r : RationalUnitaryBasisPole G) :
    RationalUnitaryPoleFactorization G (invR (r.factor G)) := by
  let b : LaurentPolynomial ℂ :=
    (LaurentPolynomial.T (-1) - LaurentPolynomial.C (r.value : ℂ)) ^ r.multiplicity
  have he : invR (r.factor G) = rationalUnramifiedFirstCoordinatePullback G r.basis b := by
    apply Subtype.ext
    funext z
    rw [unramifiedRegularInversion_apply, rationalUnramifiedFirstCoordinatePullback_eval]
    simp only [RationalUnitaryBasisPole.factor, Subalgebra.coe_pow, Pi.pow_apply, coordinateRoot_eval,
      b, map_pow, map_sub, LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_C, RingHom.id_apply,
      map_inv, Pi.inv_apply, zpow_neg_one]
    rfl
  rw [he]
  apply ofFirstCoordinateLaurent G r.basis hG b
  intro hb
  exact r.factor_ne_zero G hG ((invR).injective (by rw [he, hb, map_zero, map_zero]))

private def inversionPoleProduct (rs : List (RationalUnitaryBasisPole G)) :
    RationalUnitaryPoleFactorization G (invR (rationalUnitaryPoleProduct G rs)) := by
  induction rs with
  | nil =>
      simpa only [rationalUnitaryPoleProduct, List.map_nil, List.prod_nil, map_one] using
        ofNonvanishing G 1 (fun _ => one_ne_zero)
  | cons r rs ih =>
      have he : rationalUnitaryPoleProduct G (r :: rs) = r.factor G *
          rationalUnitaryPoleProduct G rs := rfl
      rw [he, map_mul]
      exact mul G (inversionFactor G hG r) ih

/-- Pulling back by character inversion preserves unitary pole factorability. -/
def inversion (b : R) (f : RationalUnitaryPoleFactorization G b) :
    RationalUnitaryPoleFactorization G (invR b) := by
  have he : invR b = invR (rationalUnitaryPoleProduct G f.poles) * invR f.remainder :=
    (congrArg (invR) f.factorization).trans (map_mul (invR) _ _)
  rw [he]
  exact mul G (inversionPoleProduct G hG f.poles)
    (ofNonvanishing G (invR f.remainder) (fun z => f.remainder_nonzero z⁻¹))

end RationalUnitaryPoleFactorization

namespace RationalOperatorPolePresentation

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']

/-- Compose polynomial numerators and multiply the pole-factorable
denominators. The cross identity is preserved by bilinearity. -/
def comp {a b : R} {A : X → V →ₗ[ℂ] W} {B : X → W →ₗ[ℂ] Z}
    (q : RationalOperatorPolePresentation G b B)
    (p : RationalOperatorPolePresentation G a A) :
    RationalOperatorPolePresentation G (b * a) (fun z => (B z).comp (A z)) where
  denominator := q.denominator * p.denominator
  factors := q.factors.mul G p.factors
  numerator z := (q.numerator z).comp (p.numerator z)
  polynomial := q.polynomial.comp p.polynomial
  cross z := by
    have h := congrArg₂ LinearMap.comp (q.cross z) (p.cross z)
    simpa only [Subalgebra.coe_mul, Pi.mul_apply, LinearMap.smul_comp, LinearMap.comp_smul,
      smul_smul, mul_comm] using h

/-- Tensor polynomial numerators at the same character and multiply the
pole-factorable denominators. -/
def tensor {a b : R} {A : X → V →ₗ[ℂ] W} {B : X → V' →ₗ[ℂ] W'}
    (p : RationalOperatorPolePresentation G a A)
    (q : RationalOperatorPolePresentation G b B) :
    RationalOperatorPolePresentation G (a * b) (fun z => TensorProduct.map (A z) (B z)) where
  denominator := p.denominator * q.denominator
  factors := p.factors.mul G q.factors
  numerator z := TensorProduct.map (p.numerator z) (q.numerator z)
  polynomial := p.polynomial.tensor q.polynomial
  cross z := by
    have h := congrArg₂ TensorProduct.map (p.cross z) (q.cross z)
    simpa only [Subalgebra.coe_mul, Pi.mul_apply, TensorProduct.map_smul_left,
      TensorProduct.map_smul_right, smul_smul, mul_comm] using h

/-- Carry both presentations to the inverse parameter. -/
def inversion (hG : IsConnectedReductive G) {b : R} {N : X → V →ₗ[ℂ] W}
    (p : RationalOperatorPolePresentation G b N) :
    RationalOperatorPolePresentation G (invR b) (fun z => N z⁻¹) where
  denominator := invR p.denominator
  factors := p.factors.inversion G hG _
  numerator z := p.numerator z⁻¹
  polynomial v := by
    simpa only [Set.preimage_univ] using (p.polynomial v).inversion
  cross z := p.cross z⁻¹

/-- The alternative numerator clears the original continued operator on
its displayed regular domain, even at zeros of the alternative denominator. -/
theorem clears_continuedOperator {Ω : Set X} {A : Ω → V →ₗ[ℂ] W}
    (p : RationalOperatorContinuationData Ω A)
    (q : RationalOperatorPolePresentation G p.denominator p.numerator)
    (z : p.regularRegion) :
    q.numerator z.val = (q.denominator.val z.val) • p.continuedOperator z := by
  apply smul_right_injective (V →ₗ[ℂ] W) z.property
  change p.denominator.val z.val • q.numerator z.val =
    p.denominator.val z.val • (q.denominator.val z.val • p.continuedOperator z)
  rw [q.cross z.val, RationalOperatorContinuationData.continuedOperator,
    smul_smul, smul_smul, mul_comm (p.denominator.val z.val) (q.denominator.val z.val),
    mul_assoc, mul_inv_cancel₀ z.property, mul_one]

end RationalOperatorPolePresentation
end Langlands.Plancherel

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open UnramifiedOperatorFamily

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
  (d : ScalarInverseData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)

section CompactComparison

local notation "H" => parameterScheme χ
local notation "Xχ" => unramifiedCharacters (normCharacters χ)
local notation "Rχ" => unramifiedRegularFunctions (normCharacters χ)
local notation "V₀" => compactFiber χ K ψ hψ A
local notation "V₁" => compactFiber χ K ψ' hψ' A
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q

set_option maxHeartbeats 4000000 in
/-- The two forward compact pole presentations and a cross-related inverse
scalar fraction give a pole presentation for the actual comparison. -/
def compactComparisonPolePresentation
    (c : RationalOperatorContinuationData D J) (hD : Dense D)
    (P : RationalOperatorPolePresentation H p.presentation.denominator p.presentation.numerator)
    (Q : RationalOperatorPolePresentation H d.forwardDual.presentation.denominator
      d.forwardDual.presentation.numerator)
    (a b : Rχ) (f : RationalUnitaryPoleFactorization H b)
    (hscalar : d.scalarNumerator * a = b * d.scalarDenominator) :
    RationalOperatorPolePresentation H c.denominator c.numerator := by
  let t := P.tensor H (Q.inversion H (parameterScheme_isConnectedReductive χ hG))
  let N : Xχ → V₀ →ₗ[ℂ] V₁ := fun z => a.val z • t.numerator z
  let den : Rχ := b * t.denominator
  have hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val) := t.polynomial.regular_smul a
  have hclear (z : D) : N z.val = den.val z.val • J z := by
    let z₁ : p.regularRegion := ⟨z.val, z.property.choose.1⟩
    let z₂ : d.forwardDual.regularRegion := ⟨z.val⁻¹, d.forward_regular z⟩
    let S := p.presentation.continuedOperator z₁
    let R := d.forwardDual.presentation.continuedOperator z₂
    let M : V₀ →ₗ[ℂ] V₁ := TensorProduct.map S R
    let s : ℂ := d.scalarDenominator.val z.val / d.scalarNumerator.val z.val
    have ht : t.numerator z.val = t.denominator.val z.val • M := by
      have hp := P.clears_continuedOperator H p.presentation z₁
      have hq := Q.clears_continuedOperator H d.forwardDual.presentation z₂
      calc
        t.numerator z.val = TensorProduct.map (P.numerator z₁.val) (Q.numerator z₂.val) := rfl
        _ = TensorProduct.map (P.denominator.val z₁.val • p.presentation.continuedOperator z₁)
            (Q.denominator.val z₂.val • d.forwardDual.presentation.continuedOperator z₂) :=
          congrArg₂ TensorProduct.map hp hq
        _ = (Q.denominator.val z₂.val * P.denominator.val z₁.val) • M := by
          rw [TensorProduct.map_smul_right, TensorProduct.map_smul_left, smul_smul]
        _ = t.denominator.val z.val • M :=
          congrArg (fun s : ℂ => s • M) (mul_comm _ _)
    have hJ : J z = s • M :=
      (congrArg (TensorProduct.map S) (compactReverseInverse_scalar χ hG K hK ψ hψ hψK
        ψ' hψ' hψ'K A p q d z)).trans (TensorProduct.map_smul_right s S R)
    have ha : a.val z.val = b.val z.val * s := by
      change a.val z.val = b.val z.val * (d.scalarDenominator.val z.val / d.scalarNumerator.val z.val)
      rw [← mul_div_assoc, eq_div_iff (d.numerator_nonzero z)]
      exact (mul_comm (a.val z.val) (d.scalarNumerator.val z.val)).trans
        (congrArg (fun s : Rχ => s.val z.val) hscalar)
    calc
      N z.val = a.val z.val • t.numerator z.val := rfl
      _ = a.val z.val • (t.denominator.val z.val • M) :=
        congrArg (fun L : V₀ →ₗ[ℂ] V₁ => a.val z.val • L) ht
      _ = (a.val z.val * t.denominator.val z.val) • M := smul_smul _ _ _
      _ = ((b.val z.val * s) * t.denominator.val z.val) • M :=
        congrArg (fun w : ℂ => (w * t.denominator.val z.val) • M) ha
      _ = (den.val z.val * s) • M := congrArg (fun w : ℂ => w • M) (mul_right_comm _ _ _)
      _ = den.val z.val • (s • M) := (smul_smul _ _ _).symm
      _ = den.val z.val • J z := congrArg (fun L : V₀ →ₗ[ℂ] V₁ => den.val z.val • L) hJ.symm
  refine ⟨den, f.mul H t.factors, N, hN, fun z => ?_⟩
  exact polynomial_operator_cross_eq_of_dense hD isOpen_univ isOpen_univ J N c.numerator
    den c.denominator hN c.polynomial (fun z _ => hclear z) (fun z _ => c.clears z)
      z ⟨Set.mem_univ _, Set.mem_univ _⟩

end CompactComparison
end Langlands.Plancherel.ActualCommonLeviV3
