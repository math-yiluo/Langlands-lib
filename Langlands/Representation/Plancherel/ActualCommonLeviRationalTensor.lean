import Langlands.Representation.Plancherel.ActualCommonLeviCompactTensor
import Langlands.Representation.Plancherel.RationalTensorOperators
import Langlands.Representation.Plancherel.DynamicOppositeContragredientScalar

/-! # Rationality of the particular actual normalized compact tensor -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel
namespace UnramifiedOperatorFamily

section Inversion

variable {L : Type*} [Group L] [TopologicalSpace L]
  {I : Type*} {ν : I → (L →* ℝ≥0ˣ)}
  {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {Ω : Set (unramifiedCharacters ν)}

/-- Parameter inversion preserves finite expansions in the actual regular algebra. -/
theorem IsPolynomialOn.inversion {f : Ω → V} (hf : IsPolynomialOn Ω f) :
    IsPolynomialOn ((fun z => z⁻¹) ⁻¹' Ω)
      (fun z => f ⟨z.val⁻¹, z.property⟩) := by
  obtain ⟨n, b, v, hf⟩ := hf
  exact ⟨n, fun i => unramifiedRegularInversion ν (b i), v,
    fun z => hf ⟨z.val⁻¹, z.property⟩⟩

/-- The inverse parameter still has one denominator for the whole operator. -/
theorem IsRationalOperatorOn.inversion {T : Ω → V →ₗ[ℂ] W}
    (hT : IsRationalOperatorOn Ω T) :
    IsRationalOperatorOn ((fun z => z⁻¹) ⁻¹' Ω)
      (fun z => T ⟨z.val⁻¹, z.property⟩) := by
  obtain ⟨b, hb, hpoly⟩ := hT
  exact ⟨unramifiedRegularInversion ν b, fun z => hb ⟨z.val⁻¹, z.property⟩,
    fun v => (hpoly v).inversion⟩

/-- An explicit regular ratio preserves whole-operator rationality. -/
theorem IsRationalOperatorOn.regularRatioSmul {T : Ω → V →ₗ[ℂ] W}
    (hT : IsRationalOperatorOn Ω T) (a b : unramifiedRegularFunctions ν)
    (hb : ∀ z : Ω, b.val z.val ≠ 0) :
    IsRationalOperatorOn Ω (fun z => (a.val z.val / b.val z.val) • T z) := by
  obtain ⟨c, hc, hpoly⟩ := hT
  refine ⟨b * c, fun z => mul_ne_zero (hb z) (hc z), ?_⟩
  intro v
  convert (hpoly v).regular_smul a using 1
  funext z
  simp only [LinearMap.smul_apply, Subalgebra.coe_mul, Pi.mul_apply, smul_smul]
  congr 1
  field_simp [hb z]

end Inversion
end UnramifiedOperatorFamily

namespace ActualCommonLeviRationalTensor

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor UnramifiedOperatorFamily

private theorem inverse_eq_scalar
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (R : V →ₗ[ℂ] W) (I S : W →ₗ[ℂ] V) (hR : Function.Bijective R)
    (hRI : ∀ w, R (I w) = w) (c : ℂ) (hc : c ≠ 0)
    (hRS : R.comp S = c • LinearMap.id) :
    I = ScalarComposite.inverse c S := by
  ext w
  apply hR.injective
  exact (hRI w).trans
    (congrArg (fun T : W →ₗ[ℂ] W => T w)
      (ScalarComposite.comp_inverse R S c hc hRS)).symm

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
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'


variable
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q

/-- Explicit analytic helper data for the particular actual reverse dual inverse.
The two compositions are identities of actual continued compact standard maps. -/
structure ScalarInverseData where
  forwardDual : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A.contragredient
  scalarNumerator : unramifiedRegularFunctions (normCharacters χ)
  scalarDenominator : unramifiedRegularFunctions (normCharacters χ)
  numerator_nonzero : ∀ z : D, scalarNumerator.val z.val ≠ 0
  denominator_nonzero : ∀ z : D, scalarDenominator.val z.val ≠ 0
  forward_regular : ∀ z : D, z.val⁻¹ ∈ forwardDual.regularRegion
  reverse_forward : ∀ z : D,
    (q.presentation.continuedOperator ⟨z.val⁻¹, z.property.choose.2⟩).comp
      (forwardDual.presentation.continuedOperator ⟨z.val⁻¹, forward_regular z⟩) =
        (scalarNumerator.val z.val / scalarDenominator.val z.val) • LinearMap.id
  forward_reverse : ∀ z : D,
    (forwardDual.presentation.continuedOperator ⟨z.val⁻¹, forward_regular z⟩).comp
      (q.presentation.continuedOperator ⟨z.val⁻¹, z.property.choose.2⟩) =
        (scalarNumerator.val z.val / scalarDenominator.val z.val) • LinearMap.id

variable (d : ScalarInverseData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)

/-- The compact inverse is the displayed rational scalar multiple of the
actual forward continued dual standard operator at the inverse parameter. -/
theorem compactReverseInverse_scalar (z : D) :
    compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z =
      (d.scalarDenominator.val z.val / d.scalarNumerator.val z.val) •
        d.forwardDual.presentation.continuedOperator ⟨z.val⁻¹, d.forward_regular z⟩ := by
  have h := inverse_eq_scalar
    (q.presentation.continuedOperator ⟨z.val⁻¹, z.property.choose.2⟩)
    (compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z)
    (d.forwardDual.presentation.continuedOperator ⟨z.val⁻¹, d.forward_regular z⟩)
    (compactReverse_bijective χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z)
    (compactReverseInverse_right χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z)
    (d.scalarNumerator.val z.val / d.scalarDenominator.val z.val)
    (div_ne_zero (d.numerator_nonzero z) (d.denominator_nonzero z))
    (d.reverse_forward z)
  simpa only [ScalarComposite.inverse, inv_div] using h

include d in
/-- This particular normalized tensor is rational on its genuine generic
locus. One regular scalar denominator clears the whole fixed-carrier operator. -/
theorem compactComparison_rational :
    IsRationalOperatorOn D
      (compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q) := by
  have hp := p.presentation.continuedOperator_rational.restrict
    (show D ⊆ p.regularRegion from fun _ hz => hz.choose.1)
  have hdual := d.forwardDual.presentation.continuedOperator_rational
  have hinv := hdual.inversion
  have hr := hinv.restrict
    (show D ⊆ (fun z => z⁻¹) ⁻¹' d.forwardDual.regularRegion from
      fun z hz => d.forward_regular ⟨z, hz⟩)
  have hi := hr.regularRatioSmul d.scalarDenominator d.scalarNumerator d.numerator_nonzero
  have ht := hp.tensor hi
  have heq : compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q =
      (fun z : D => TensorProduct.map
        (p.presentation.continuedOperator ⟨z.val, z.property.choose.1⟩)
        ((d.scalarDenominator.val z.val / d.scalarNumerator.val z.val) •
          d.forwardDual.presentation.continuedOperator ⟨z.val⁻¹, d.forward_regular z⟩)) := by
    funext z
    exact congrArg
      (TensorProduct.map (p.presentation.continuedOperator ⟨z.val, z.property.choose.1⟩))
      (compactReverseInverse_scalar χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q d z)
  rw [heq]
  exact ht

end ActualCommonLeviRationalTensor
end Langlands.Plancherel
