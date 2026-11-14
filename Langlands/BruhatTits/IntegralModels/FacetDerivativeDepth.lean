import Langlands.BruhatTits.IntegralModels.FacetRootDatum
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint

/-! # Facet derivative roots and the doubled-root depth criterion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building Geometry.Building.AffineRootSystem

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The actual relative characters whose depth-zero filtration survives
modulo the positive-depth filtration and the full doubled-root group. -/
def facetDepthRoots (x : B.Apartment) : Set (characterLattice B.S) :=
  {a | a ∈ relativeRoots B.i ∧
    ¬ (B.filtration x a 0 : Set (rationalPoints G)) ⊆
      (B.filtrationPlus x a 0 : Set (rationalPoints G)) *
        (doubleRootGroupPoints B.i a : Set (rationalPoints G))}

/-- The defining ordinary affine-root test, in the point/depth indexing.
The doubled-root factor is retained even for multipliable roots. -/
theorem affineFunctional_mem_affineRoots_iff_depth
    (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    B.apartment.affineFunctional a x r ∈ B.affineRoots ↔
      ¬ (B.filtration x a r : Set (rationalPoints G)) ⊆
        (B.filtrationPlus x a r : Set (rationalPoints G)) *
          (doubleRootGroupPoints B.i a : Set (rationalPoints G)) := by
  change B.apartment.affineFunctional a x r ∈ B.affineRoots ↔
    ¬ (B.apartment.filtration x a r : Set (rationalPoints G)) ⊆
      (B.apartment.filtrationPlus x a r : Set (rationalPoints G)) *
        (doubleRootGroupPoints B.i a : Set (rationalPoints G))
  rw [B.apartment.filtration_eq_affineRootGroup a x r,
    B.apartment.filtrationPlus_eq_affineRootGroupPlus a x r]
  constructor
  · rintro ⟨b, hlin, hnot⟩
    have hb : b = a :=
      SpecialCompact.rootForm_injective_of_split
        B.isMaximalSplitTorus.isSplitSubtorus.1 B.i hlin.symm
    simpa only [hb] using hnot
  · intro hnot
    exact ⟨a, rfl, hnot⟩

/-- A derivative root of the full facet of `x` is detected by the unique
affine functional with that derivative and value zero at `x`. -/
theorem mem_facetDerivativeRoots_facet_iff_affineFunctional
    (x : B.Apartment) (a : relativeRoots B.i) :
    a.val ∈ facetDerivativeRoots B (facet B.affineRoots x) ↔
      B.apartment.affineFunctional a x 0 ∈ B.affineRoots := by
  constructor
  · rintro ⟨ha, ψ, hψ, hlin, hzero⟩
    have heq : ψ = B.apartment.affineFunctional a x 0 :=
      AffineMap.ext_linear (p := x) hlin (by
        simpa using hzero x (mem_facet_self B.affineRoots x))
    rwa [← heq]
  · intro hψ
    exact ⟨a.property, B.apartment.affineFunctional a x 0, hψ, rfl,
      facet_subset_hyperplane ⟨hψ, by simp⟩⟩

/-- The exact depth-zero criterion for an actual facet derivative root. -/
theorem mem_facetDerivativeRoots_facet_iff_depth
    (x : B.Apartment) (a : relativeRoots B.i) :
    a.val ∈ facetDerivativeRoots B (facet B.affineRoots x) ↔
      ¬ (B.filtration x a 0 : Set (rationalPoints G)) ⊆
        (B.filtrationPlus x a 0 : Set (rationalPoints G)) *
          (doubleRootGroupPoints B.i a : Set (rationalPoints G)) :=
  (mem_facetDerivativeRoots_facet_iff_affineFunctional B x a).trans
    (affineFunctional_mem_affineRoots_iff_depth B x a 0)

/-- The actual-character derivative-root set equals the doubled-root
depth support, without any apartment-axiom premise. -/
theorem facetDerivativeRoots_eq_facetDepthRoots (x : B.Apartment) :
    facetDerivativeRoots B (facet B.affineRoots x) = facetDepthRoots B x := by
  ext a
  constructor
  · intro ha
    have haroot : a ∈ relativeRoots B.i := ha.choose
    exact ⟨haroot,
      (mem_facetDerivativeRoots_facet_iff_depth B x ⟨a, haroot⟩).mp ha⟩
  · rintro ⟨ha, hdepth⟩
    exact (mem_facetDerivativeRoots_facet_iff_depth B x ⟨a, ha⟩).mpr hdepth

end Langlands.BruhatTits.IntegralModels
