import Langlands.BruhatTits.IntegralModels.FacetDerivativeLocalization
import Langlands.Geometry.Building.BuildingFacetIncidence

/-! # Actual integral root supports detect incident facet order -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building Geometry.Building.AffineRootSystem
open GroupScheme.RealTorusSpace

private theorem nonnegativeLinearRoots_iff_at
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Φ : Set (Module.Dual ℝ V)} {C : Set V} {w : V}
    (hC : IsFacet (linearRootArrangement Φ) C) (hw : w ∈ C)
    (a : Module.Dual ℝ V) :
    a ∈ nonnegativeLinearRoots Φ C ↔ a ∈ Φ ∧ 0 ≤ a w := by
  obtain ⟨z, rfl⟩ := hC
  change (a ∈ Φ ∧ ∀ y ∈ facet (linearRootArrangement Φ) z, 0 ≤ a y) ↔ _
  refine and_congr_right fun ha => ⟨fun h => h w hw, fun h y hy => ?_⟩
  have ha' : a.toAffineMap ∈ linearRootArrangement Φ := ⟨a, ha, rfl⟩
  have hy' : SignType.sign (a z) = SignType.sign (a y) := hy a.toAffineMap ha'
  have hw' : SignType.sign (a z) = SignType.sign (a w) := hw a.toAffineMap ha'
  rw [← sign_nonneg_iff, ← hy', hw', sign_nonneg_iff]
  exact h

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G) {x : B.Apartment}

/-- Actual facet derivative characters with nonnegative integer pairing with
the integral representative of the given incident full facet. -/
def incidentFacetRootSupport (F : IncidentAffineFacet B.affineRoots x) :
    Set (characterLattice B.S) :=
  {a | a ∈ facetDerivativeRoots B (facet B.affineRoots x) ∧
    0 ≤ latticePairing B.S a (incidentFacetCocharacter B F)}

/-- Integer-pairing support is exactly the nonnegative support of the actual
root forms on the whole derivative facet. -/
theorem mem_incidentFacetRootSupport_iff
    (F : IncidentAffineFacet B.affineRoots x) (a : relativeRoots B.i) :
    a.val ∈ incidentFacetRootSupport B F ↔
      rootForm B.i a ∈
        nonnegativeLinearRoots (derivativeRoots (vanishingRoots B.affineRoots x))
          (incidentFacetDerivative F).val := by
  rw [nonnegativeLinearRoots_iff_at (incidentFacetDerivative F).property
    (incidentFacetCocharacter_mem B F)]
  change (a.val ∈ facetDerivativeRoots B (facet B.affineRoots x) ∧
    0 ≤ latticePairing B.S a.val (incidentFacetCocharacter B F)) ↔ _
  simp only [mem_facetDerivativeRoots_facet_iff, rootForm_mk, eval_tmul, one_mul,
    Int.cast_nonneg_iff]

/-- Inclusion of actual character supports is equivalent to inclusion of
actual derivative-form supports. -/
theorem incidentFacetRootSupport_subset_iff
    (F H : IncidentAffineFacet B.affineRoots x) :
    incidentFacetRootSupport B H ⊆ incidentFacetRootSupport B F ↔
      nonnegativeLinearRoots (derivativeRoots (vanishingRoots B.affineRoots x))
          (incidentFacetDerivative H).val ⊆
        nonnegativeLinearRoots (derivativeRoots (vanishingRoots B.affineRoots x))
          (incidentFacetDerivative F).val := by
  constructor
  · intro h f hf
    have hf' : f ∈ rootForm B.i '' {a : relativeRoots B.i |
        a.val ∈ facetDerivativeRoots B (facet B.affineRoots x)} := by
      rw [image_rootForm_facetDerivativeRoots]
      exact hf.1
    obtain ⟨a, _, rfl⟩ := hf'
    exact (mem_incidentFacetRootSupport_iff B F a).mp
      (h ((mem_incidentFacetRootSupport_iff B H a).mpr hf))
  · intro h χ hχ
    let a : relativeRoots B.i := ⟨χ, hχ.1.choose⟩
    exact (mem_incidentFacetRootSupport_iff B F a).mpr
      (h ((mem_incidentFacetRootSupport_iff B H a).mp hχ))

/-- Reverse inclusion of actual integer-pairing supports detects the original
face relation on incident full facets. -/
theorem isFaceOf_iff_incidentFacetRootSupport_subset
    (hneg : ∀ ψ ∈ B.affineRoots, -ψ ∈ B.affineRoots)
    (F H : IncidentAffineFacet B.affineRoots x) :
    IsFaceOf B.affineRoots F.val H.val ↔
      incidentFacetRootSupport B H ⊆ incidentFacetRootSupport B F :=
  (isFaceOf_iff_incident_nonnegativeLinearRoots_subset hneg F H).trans
    (incidentFacetRootSupport_subset_iff B F H).symm

/-- The original incident facet order embeds in reverse inclusion of actual
facet derivative characters with nonnegative integral pairing. -/
def incidentFacetRootSupportOrderEmbedding
    (hneg : ∀ ψ ∈ B.affineRoots, -ψ ∈ B.affineRoots) (x : B.Apartment) :
    @OrderEmbedding (IncidentAffineFacet B.affineRoots x)
      (OrderDual (Set (characterLattice B.S)))
      ⟨fun F H => IsFaceOf B.affineRoots F.val H.val⟩ inferInstance where
  toFun F := OrderDual.toDual (incidentFacetRootSupport B F)
  inj' F H h := by
    have h' : incidentFacetRootSupport B F = incidentFacetRootSupport B H :=
      congrArg OrderDual.ofDual h
    apply Subtype.ext
    exact IsFaceOf.antisymm
      ((isFaceOf_iff_incidentFacetRootSupport_subset B hneg F H).mpr h'.ge)
      ((isFaceOf_iff_incidentFacetRootSupport_subset B hneg H F).mpr h'.le)
  map_rel_iff' {F H} :=
    (isFaceOf_iff_incidentFacetRootSupport_subset B hneg F H).symm

@[simp] theorem incidentFacetRootSupportOrderEmbedding_apply
    (hneg : ∀ ψ ∈ B.affineRoots, -ψ ∈ B.affineRoots) (x : B.Apartment)
    (F : IncidentAffineFacet B.affineRoots x) :
    incidentFacetRootSupportOrderEmbedding B hneg x F =
      OrderDual.toDual (incidentFacetRootSupport B F) := rfl

end Langlands.BruhatTits.IntegralModels
