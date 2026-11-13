import Langlands.Geometry.Building.AffineFacetRootCount
import Langlands.Geometry.Building.IntegerBuildingFacetOrder
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Maximal full facets in prescribed subsets of the integer-valued building -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)

/-- The actual affine-root derivatives form a finite set because the actual
relative roots of the supplied maximal split torus form a finite set. -/
theorem finite_derivativeRoots :
    (AffineRootSystem.derivativeRoots B.affineRoots).Finite := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : Finite (relativeRoots B.i) :=
    (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i).to_subtype
  apply (Set.finite_range (rootForm B.i)).subset
  rintro _ ⟨ψ, ⟨α, hlin, _⟩, rfl⟩
  exact ⟨α, hlin.symm⟩

/-- The vanishing-root count on the original reduced quotient. Normalizer
coordinate changes preserve it, so it descends through the original relation. -/
def pointVanishingRootCount : B.ReducedBuilding → ℕ :=
  Quotient.lift
    (fun p : rationalPoints G × B.Apartment =>
      AffineRootSystem.vanishingRootCount B.affineRoots p.2)
    (by
      intro p q hpq
      obtain ⟨n, hn, _⟩ := hpq
      rw [← hn]
      exact (AffineRootSystem.vanishingRootCount_apply
        (B.apartment.normalizerAffineEquiv_mem_rootStabilizer n) p.2).symm)

@[simp]
theorem pointVanishingRootCount_translatedApartmentMap
    (g : rationalPoints G) (a : B.Apartment) :
    B.pointVanishingRootCount (B.translatedApartmentMap g a) =
      AffineRootSystem.vanishingRootCount B.affineRoots a := rfl

/-- The quotient count is constant on each original full facet. -/
theorem pointVanishingRootCount_eq_of_mem_mem {F : Set B.ReducedBuilding}
    (hF : B.IsFacet F) {x y : B.ReducedBuilding} (hx : x ∈ F) (hy : y ∈ F) :
    B.pointVanishingRootCount x = B.pointVanishingRootCount y := by
  obtain ⟨g, Fa, ⟨a, rfl⟩, rfl⟩ := hF
  obtain ⟨b, hb, rfl⟩ := hx
  obtain ⟨c, hc, rfl⟩ := hy
  change AffineRootSystem.vanishingRootCount B.affineRoots b =
    AffineRootSystem.vanishingRootCount B.affineRoots c
  exact AffineRootSystem.vanishingRootCount_eq_of_facetRel
    ((AffineRootSystem.facetRel_equivalence B.affineRoots).trans
      ((AffineRootSystem.facetRel_equivalence B.affineRoots).symm hb) hc)

/-- The common value of the quotient count on a full facet. -/
def facetVanishingRootCount (F : B.BuildingFacet) : ℕ :=
  B.pointVanishingRootCount (Classical.choose (F.property.nonempty B))

theorem facetVanishingRootCount_eq_of_mem (F : B.BuildingFacet)
    {x : B.ReducedBuilding} (hx : x ∈ F.val) :
    B.facetVanishingRootCount F = B.pointVanishingRootCount x :=
  B.pointVanishingRootCount_eq_of_mem_mem F.property
    (Classical.choose_spec (F.property.nonempty B)) hx

/-- Every presentation of a full facet computes its count at its affine
representative. -/
theorem facetVanishingRootCount_eq_of_image (F : B.BuildingFacet)
    (g : rationalPoints G) (a : B.Apartment)
    (hF : F.val = B.translatedApartmentMap g ''
      AffineRootSystem.facet B.affineRoots a) :
    B.facetVanishingRootCount F =
      AffineRootSystem.vanishingRootCount B.affineRoots a := by
  rw [B.facetVanishingRootCount_eq_of_mem F
    (hF ▸ Set.mem_image_of_mem _ (AffineRootSystem.mem_facet_self B.affineRoots a))]
  rfl

/-- Strict upward incidence strictly decreases the count of a full facet. -/
theorem facetVanishingRootCount_lt_of_facetPrecedes
    {F C : B.BuildingFacet} (hFC : B.FacetPrecedes F C) (hne : F ≠ C) :
    B.facetVanishingRootCount C < B.facetVanishingRootCount F := by
  obtain ⟨g, Fa, Ca, ⟨⟨a, rfl⟩, b, rfl, hsub⟩, hF, hC⟩ := hFC
  rw [B.facetVanishingRootCount_eq_of_image F g a hF,
    B.facetVanishingRootCount_eq_of_image C g b hC]
  apply AffineRootSystem.vanishingRootCount_lt_of_mem_facetClosure
    B.finite_derivativeRoots (hsub (AffineRootSystem.mem_facet_self _ _))
  intro hab
  apply hne
  apply Subtype.ext
  rw [hF, hC, AffineRootSystem.facet_eq_facet_iff.mpr hab]

/-- In any chosen subset of full facets, every member has a maximal member
above it for the original incidence relation. -/
theorem exists_maximal_facet_in_subset (s : Set B.BuildingFacet)
    (F : B.BuildingFacet) (hF : F ∈ s) :
    ∃ C : B.BuildingFacet, C ∈ s ∧ B.FacetPrecedes F C ∧
      ∀ E : B.BuildingFacet, E ∈ s → B.FacetPrecedes C E → E = C := by
  classical
  let P : ℕ → Prop := fun n => ∃ C : B.BuildingFacet,
    C ∈ s ∧ B.FacetPrecedes F C ∧ B.facetVanishingRootCount C = n
  have hex : ∃ n, P n :=
    ⟨B.facetVanishingRootCount F, F, hF, B.facetPrecedes_refl F, rfl⟩
  obtain ⟨C, hCs, hFC, hcount⟩ := Nat.find_spec hex
  refine ⟨C, hCs, hFC, fun E hEs hCE => ?_⟩
  by_contra hne
  have hlt := B.facetVanishingRootCount_lt_of_facetPrecedes hCE (Ne.symm hne)
  have hmin := Nat.find_min' hex
    (show P (B.facetVanishingRootCount E) from
      ⟨E, hEs, B.facetPrecedes_trans hFC hCE, rfl⟩)
  exact (not_lt_of_ge (hcount.symm ▸ hmin)) hlt

end IntegerValuationBuildingData

/-- Maximal extensions exist inside every specified subset of the original
full facets, starting from each of its members. -/
def IntegerBuildingMaximalFacetsStatement : Prop :=
  ∀ (k : Type u) [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G) (s : Set B.BuildingFacet)
    (F : B.BuildingFacet), F ∈ s →
      ∃ C : B.BuildingFacet, C ∈ s ∧ B.FacetPrecedes F C ∧
        ∀ E : B.BuildingFacet, E ∈ s → B.FacetPrecedes C E → E = C

theorem integerBuildingMaximalFacets : IntegerBuildingMaximalFacetsStatement.{u} := by
  intro k _ v G _ B s F hF
  exact B.exists_maximal_facet_in_subset s F hF

end Langlands.Geometry.Building
