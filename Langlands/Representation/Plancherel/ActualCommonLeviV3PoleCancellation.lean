import Langlands.Representation.Plancherel.RationalUnitaryOperatorCancellation
import Langlands.Representation.Plancherel.ActualCommonLeviV3GermProof

/-! # Actual common-Levi regular germs from supplied root support and bounds -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV uW uE

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped NNReal CategoryTheory.MonObj TensorProduct

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

section NormedModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hG : IsConnectedReductive G)

local instance modelCancellationPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (rs : List (RationalUnitaryBasisPole G))
  (N : unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul) → V →ₗ[ℂ] W)
  (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
  (e : W ≃ₗ[ℂ] E)
  (d : unramifiedRegularFunctions (fun a => (rationalNormCharacters G a).toMul))
  (hbound : HasClearedUnitaryBound G
    (fun z => e.toLinearMap.comp (N z)) (rationalUnitaryPoleProduct G rs * d))

/-- Cancel the specified poles using a normed model while retaining the
original, possibly nontopological, target carrier. -/
def rationalUnitaryCancelledModelOperator
    (z : unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)) : V →ₗ[ℂ] W :=
  e.symm.toLinearMap.comp
    (rationalUnitaryCancelledOperator G hG rs (fun z => e.toLinearMap.comp (N z))
      (hN.postcomp e.toLinearMap) d hbound z)

theorem rationalUnitaryCancelledModelOperator_isPolynomial :
    IsPolynomialOperatorOn Set.univ
      (fun z => rationalUnitaryCancelledModelOperator G hG rs N hN e d hbound z.val) :=
  (rationalUnitaryCancelledOperator_isPolynomial G hG rs
    (fun z => e.toLinearMap.comp (N z)) (hN.postcomp e.toLinearMap) d hbound).postcomp
      e.symm.toLinearMap

theorem rationalUnitaryCancelledModelOperator_spec
    (z : unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)) :
    N z = (rationalUnitaryPoleProduct G rs).val z •
      rationalUnitaryCancelledModelOperator G hG rs N hN e d hbound z := by
  apply LinearMap.ext
  intro v
  apply e.injective
  have he := congrArg (fun T : V →ₗ[ℂ] E => T v)
    (rationalUnitaryCancelledOperator_spec G hG rs
      (fun z => e.toLinearMap.comp (N z)) (hN.postcomp e.toLinearMap) d hbound z)
  simpa only [rationalUnitaryCancelledModelOperator, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearMap.smul_apply, map_smul,
    LinearEquiv.apply_symm_apply] using he

end NormedModel

private theorem cancel_cleared_operator_scalar
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {s d : ℂ} (hs : s ≠ 0) {N Q J : W}
    (hN : N = s • Q) (hJ : N = (s * d) • J) :
    Q = d • J :=
  smul_right_injective W hs (hN.symm.trans (hJ.trans (mul_smul s d J)))

namespace ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor

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

set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "R" => unramifiedRegularFunctions (normCharacters χ)
set_option hygiene false in
local notation "V₀" => compactFiber χ K ψ hψ A
set_option hygiene false in
local notation "V₁" => compactFiber χ K ψ' hψ' A
set_option hygiene false in
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
set_option hygiene false in
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q

variable
  (rs : List (RationalUnitaryBasisPole (parameterScheme χ)))
  (N : X → V₀ →ₗ[ℂ] V₁)
  (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (e : V₁ ≃ₗ[ℂ] E)
  (d : R)
  (hbound : HasClearedUnitaryBound (parameterScheme χ)
    (fun z => e.toLinearMap.comp (N z)) (rationalUnitaryPoleProduct (parameterScheme χ) rs * d))

/-- The polynomial numerator of the actual compact tensor after the supplied
unitary root factors have been canceled in a normed model. -/
def cancelledCompactNumerator : X → V₀ →ₗ[ℂ] V₁ :=
  rationalUnitaryCancelledModelOperator (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG) rs N hN e d hbound

theorem cancelledCompactNumerator_isPolynomial :
    IsPolynomialOperatorOn Set.univ
      (fun z => cancelledCompactNumerator χ hG A K ψ hψ ψ' hψ' rs N hN e d hbound z.val) :=
  rationalUnitaryCancelledModelOperator_isPolynomial (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG) rs N hN e d hbound

theorem cancelledCompactNumerator_isLocalRepresentative
    (hden : ∀ z : D, (rationalUnitaryPoleProduct (parameterScheme χ) rs * d).val z.val ≠ 0)
    (hnum : ∀ z : D,
      N z.val = (rationalUnitaryPoleProduct (parameterScheme χ) rs * d).val z.val • J z) :
    IsLocalRepresentative χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q
      {z : X | d.val z ≠ 0}
      (cancelledCompactNumerator χ hG A K ψ hψ ψ' hψ' rs N hN e d hbound) d := by
  refine ⟨isOpen_ne_fun (continuous_unramifiedRegularFunction _ d) continuous_const,
    cancelledCompactNumerator_isPolynomial χ hG A K ψ hψ ψ' hψ' rs N hN e d hbound,
    fun _ hz => hz, ?_⟩
  intro z hz
  have hs : (rationalUnitaryPoleProduct (parameterScheme χ) rs).val z.val ≠ 0 :=
    (mul_ne_zero_iff.mp (hden z)).1
  exact cancel_cleared_operator_scalar (W := V₀ →ₗ[ℂ] V₁)
    (d := d.val z.val) (N := N z.val) hs
    (rationalUnitaryCancelledModelOperator_spec (parameterScheme χ)
      (parameterScheme_isConnectedReductive χ hG) rs N hN e d hbound z.val) (hnum z)

theorem regularGermAt_of_unitary_pole_data
    (hden : ∀ z : D, (rationalUnitaryPoleProduct (parameterScheme χ) rs * d).val z.val ≠ 0)
    (hnum : ∀ z : D,
      N z.val = (rationalUnitaryPoleProduct (parameterScheme χ) rs * d).val z.val • J z)
    (hd : ∀ z : Xu, d.val (unitaryParameter χ z) ≠ 0) (z : Xu) :
    RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q (unitaryParameter χ z)
      ((d.val (unitaryParameter χ z))⁻¹ •
        cancelledCompactNumerator χ hG A K ψ hψ ψ' hψ' rs N hN e d hbound
          (unitaryParameter χ z)) :=
  ⟨{z : X | d.val z ≠ 0},
    cancelledCompactNumerator χ hG A K ψ hψ ψ' hψ' rs N hN e d hbound,
    d, hd z,
    cancelledCompactNumerator_isLocalRepresentative χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K
      p q rs N hN e d hbound hden hnum, rfl⟩

end ActualCommonLeviV3
end Langlands.Plancherel
