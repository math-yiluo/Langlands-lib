import Langlands.Representation.Plancherel.ContinuedIntertwiningScalar
import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericLocus

/-! # Denominator refinement for the actual common-Levi standard continuation -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel

namespace UnramifiedOperatorFamily.RationalOperatorContinuationData

variable {L : Type*} [Group L] [TopologicalSpace L]
  {I : Type*} {ν : I → (L →* ℝ≥0ˣ)}
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {Ω : Set (unramifiedCharacters ν)} {A : Ω → V →ₗ[ℂ] W}
  (p : RationalOperatorContinuationData Ω A) (b : unramifiedRegularFunctions ν)

/-- Multiply both parts of a whole-operator presentation by one regular
factor, restricting the starting region to its nonzero locus. -/
def withDenominatorFactor :
    RationalOperatorContinuationData (Ω ∩ {z | b.val z ≠ 0})
      (fun z => A ⟨z.val, z.property.1⟩) where
  denominator := b * p.denominator
  numerator z := b.val z • p.numerator z
  denominator_nonzero z := mul_ne_zero z.property.2 (p.denominator_nonzero ⟨z.val, z.property.1⟩)
  polynomial := p.polynomial.regular_smul b
  clears z := by
    change b.val z.val • p.numerator z.val =
      (b.val z.val * p.denominator.val z.val) • A ⟨z.val, z.property.1⟩
    rw [p.clears ⟨z.val, z.property.1⟩, smul_smul]

/-- The original denominator and added factor must both be nonzero. -/
theorem withDenominatorFactor_regularRegion :
    (p.withDenominatorFactor b).regularRegion = p.regularRegion ∩ {z | b.val z ≠ 0} := by
  ext z
  change b.val z * p.denominator.val z ≠ 0 ↔ p.denominator.val z ≠ 0 ∧ b.val z ≠ 0
  exact mul_ne_zero_iff.trans and_comm

/-- The refined presentation gives the original value on its regular region. -/
theorem withDenominatorFactor_continuedOperator (z : (p.withDenominatorFactor b).regularRegion)
    (hz : z.val ∈ p.regularRegion) :
    (p.withDenominatorFactor b).continuedOperator z = p.continuedOperator ⟨z.val, hz⟩ := by
  have hb : b.val z.val ≠ 0 :=
    ((p.withDenominatorFactor_regularRegion b).subset z.property).2
  have hd : p.denominator.val z.val ≠ 0 := hz
  have he : (b.val z.val * p.denominator.val z.val)⁻¹ * b.val z.val =
      (p.denominator.val z.val)⁻¹ := by
    field_simp
  change (b.val z.val * p.denominator.val z.val)⁻¹ • (b.val z.val • p.numerator z.val) =
    (p.denominator.val z.val)⁻¹ • p.numerator z.val
  rw [smul_smul, he]

end UnramifiedOperatorFamily.RationalOperatorContinuationData

universe u uV

namespace ActualCommonLeviV3

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviRationalTensor UnramifiedOperatorFamily

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

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (b : unramifiedRegularFunctions (normCharacters χ)) (hb : b ≠ 0)

include hb in
/-- Retain the same standard integral and modulus on the nonzero locus of an
extra factor. This locus meets the original open convergence region. -/
def continuedPairWithDenominatorFactor :
    ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A where
  modulus := p.modulus
  region := p.region ∩ {z | b.val z ≠ 0}
  isOpen_region := p.isOpen_region.inter
    (isOpen_ne_fun (continuous_unramifiedRegularFunction (normCharacters χ) b) continuous_const)
  nonempty_region := by
    obtain ⟨z, hz, hzb⟩ := rationalUnramifiedRegular_exists_ne_zero_of_isOpen (parameterScheme χ)
      (DynamicOppositeCanonicalScalar.parameterProjection_continuous χ)
      (parameterScheme_isConnectedReductive χ hG) b hb p.isOpen_region p.nonempty_region
    exact ⟨z, hz, hzb⟩
  converges := fun _ hz => p.converges hz.1
  presentation := p.presentation.withDenominatorFactor b

local notation "p₁" =>
  continuedPairWithDenominatorFactor χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p b hb

/-- The refined actual continued pair is regular where the original pair is
regular and the added factor is nonzero. -/
theorem continuedPairWithDenominatorFactor_regularRegion :
    (p₁).regularRegion = p.regularRegion ∩ {z | b.val z ≠ 0} :=
  p.presentation.withDenominatorFactor_regularRegion b

/-- At each parameter of the refined region the compact standard operator
agrees with its original continued value. -/
theorem continuedPairWithDenominatorFactor_continuedOperator
    (z : (p₁).regularRegion) (hz : z.val ∈ p.regularRegion) :
    (p₁).presentation.continuedOperator z = p.presentation.continuedOperator ⟨z.val, hz⟩ :=
  p.presentation.withDenominatorFactor_continuedOperator b z hz

variable (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

set_option quotPrecheck false in
local notation "O" =>
  (regularLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q ∩ {z | b.val z ≠ 0} :
    Set (unramifiedCharacters (normCharacters χ)))
local notation "R₁" =>
  regularLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p₁ q
local notation "D₁" =>
  genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p₁ q

/-- Refining the forward pair cuts the simultaneous regular locus by the
extra nonzero condition. The reverse pair remains the original one. -/
theorem refinedRegularLocus_eq : R₁ = O := by
  ext z
  have h := continuedPairWithDenominatorFactor_regularRegion χ hG K hK ψ hψ hψK
    ψ' hψ' hψ'K A p b hb
  constructor
  · intro hz
    have ht := h.subset (show z ∈ (p₁).regularRegion from hz.1)
    exact ⟨⟨ht.1, hz.2⟩, ht.2⟩
  · intro hz
    exact ⟨h.symm.subset ⟨hz.1.1, hz.2⟩, hz.1.2⟩

private theorem denseGenericLocus_of_refinement
    (hp : ∀ z : O, Function.Bijective (p.presentation.continuedOperator ⟨z.val, z.property.1.1⟩))
    (hq : ∀ z : O, Function.Bijective (q.presentation.continuedOperator ⟨z.val⁻¹, z.property.1.2⟩)) :
    HasDenseGenericLocus χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p₁ q := by
  let invDen := unramifiedRegularInversion (normCharacters χ) q.presentation.denominator
  let c : unramifiedRegularFunctions (normCharacters χ) := b * p.presentation.denominator * invDen
  have hp₀ := p.presentation.denominator_ne_zero p.nonempty_region
  have hq₀ := q.presentation.denominator_ne_zero q.nonempty_region
  have hi : invDen ≠ 0 := by
    intro h
    exact hq₀ ((unramifiedRegularInversion (normCharacters χ)).injective
      (h.trans (map_zero (unramifiedRegularInversion (normCharacters χ))).symm))
  let := rationalUnramifiedRegularFunctions_isDomain (parameterScheme χ)
    (DynamicOppositeCanonicalScalar.parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG)
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero hb hp₀) hi
  refine hasDenseGenericLocus_of_regular_nonzero_subset χ hG A K hK
    ψ hψ hψK ψ' hψ' hψ'K p₁ q c hc ?_
  intro z hz
  change (b.val z * p.presentation.denominator.val z) * q.presentation.denominator.val z⁻¹ ≠ 0 at hz
  have hcz := mul_ne_zero_iff.mp hz
  have hbz := mul_ne_zero_iff.mp hcz.1
  have hzO : z ∈ O := ⟨⟨hbz.2, hcz.2⟩, hbz.1⟩
  have hzR : z ∈ R₁ := (refinedRegularLocus_eq χ hG K hK ψ hψ hψK
    ψ' hψ' hψ'K A p b hb q).symm.subset hzO
  have he := continuedPairWithDenominatorFactor_continuedOperator χ hG K hK ψ hψ hψK
    ψ' hψ' hψ'K A p b hb ⟨z, hzR.1⟩ hzO.1.1
  have he' := congrArg (fun T : _ →ₗ[ℂ] _ => Function.Bijective T) he
  exact ⟨hzR, he'.mpr (hp ⟨z, hzO⟩), hq ⟨z, hzO⟩⟩

/-- From scalar identities on the intersection of the original regular
loci with a nonzero locus, construct the scalar inverse data on the whole
genuine generic locus of the refined pair. The same intersection supplies
all ambient and unitary density clauses. -/
def scalarInverseDataOfDenominatorFactor
    (s : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A.contragredient)
    (a c : unramifiedRegularFunctions (normCharacters χ))
    (ha : ∀ z : O, a.val z.val ≠ 0) (hc : ∀ z : O, c.val z.val ≠ 0)
    (hs : ∀ z : O, z.val⁻¹ ∈ s.regularRegion)
    (hp : ∀ z : O, Function.Bijective (p.presentation.continuedOperator ⟨z.val, z.property.1.1⟩))
    (hqs : ∀ z : O, (q.presentation.continuedOperator ⟨z.val⁻¹, z.property.1.2⟩).comp
      (s.presentation.continuedOperator ⟨z.val⁻¹, hs z⟩) =
        (a.val z.val / c.val z.val) • LinearMap.id)
    (hsq : ∀ z : O, (s.presentation.continuedOperator ⟨z.val⁻¹, hs z⟩).comp
      (q.presentation.continuedOperator ⟨z.val⁻¹, z.property.1.2⟩) =
        (a.val z.val / c.val z.val) • LinearMap.id) :
    {_d : ScalarInverseData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p₁ q //
      HasDenseGenericLocus χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p₁ q} := by
  let o (z : D₁) : O := ⟨z.val, (refinedRegularLocus_eq χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
    A p b hb q).subset z.property.choose⟩
  refine ⟨{
    forwardDual := s
    scalarNumerator := a
    scalarDenominator := c
    numerator_nonzero := fun z => ha (o z)
    denominator_nonzero := fun z => hc (o z)
    forward_regular := fun z => hs (o z)
    reverse_forward := fun z => hqs (o z)
    forward_reverse := fun z => hsq (o z)
  }, denseGenericLocus_of_refinement χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p b hb q hp ?_⟩
  intro z
  exact ScalarComposite.bijective _ _ _ (div_ne_zero (ha z) (hc z)) (hsq z) (hqs z)

end ActualCommonLeviV3
end Langlands.Plancherel
