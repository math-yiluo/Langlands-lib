import Langlands.Geometry.Building.GaloisFixedFacetIncidence
import Langlands.Geometry.Building.IntegerBuildingMaximalFacets

/-! # Maximal facets meeting the actual Galois fixed set -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]

variable {v : Valuation K (WithZero (Multiplicative ℤ))}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i)
    (IntegerValuation.order v))
  (hD : GaloisStable k K i D)
  (hG : IsConnectedReductive (baseChanged k K G))
  (hi : IsMaximalSplitTorus
    (T := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (C : CentralizerDatum
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (h6 : IntegerValuation.IsOmegaCompatible v D C)

include hG hi C h6

local notation "B" => integerBuildingData D hG hi C h6
/-- Maximality among the original full facets that meet the actual fixed set. -/
def IsMaximalGaloisFacet (E : GaloisFacet k K i D hD hG hi C h6) : Prop :=
  ∀ F : GaloisFacet k K i D hD hG hi C h6,
    GaloisFacetPrecedes k K i D hD hG hi C h6 E F → F = E

theorem galoisFacetPrecedes_refl (F : GaloisFacet k K i D hD hG hi C h6) :
    GaloisFacetPrecedes k K i D hD hG hi C h6 F F :=
  (B).facetPrecedes_refl F.val

theorem galoisFacetPrecedes_trans
    {F E H : GaloisFacet k K i D hD hG hi C h6}
    (hFE : GaloisFacetPrecedes k K i D hD hG hi C h6 F E)
    (hEH : GaloisFacetPrecedes k K i D hD hG hi C h6 E H) :
    GaloisFacetPrecedes k K i D hD hG hi C h6 F H :=
  (B).facetPrecedes_trans hFE hEH

theorem galoisFacetPrecedes_antisymm
    {F E : GaloisFacet k K i D hD hG hi C h6}
    (hFE : GaloisFacetPrecedes k K i D hD hG hi C h6 F E)
    (hEF : GaloisFacetPrecedes k K i D hD hG hi C h6 E F) : F = E :=
  Subtype.ext ((B).facetPrecedes_antisymm hFE hEF)

/-- Every Gamma-facet has a maximal Gamma-facet incident above it. -/
theorem exists_maximal_galoisFacet_above
    (F : GaloisFacet k K i D hD hG hi C h6) :
    ∃ E : GaloisFacet k K i D hD hG hi C h6,
      GaloisFacetPrecedes k K i D hD hG hi C h6 F E ∧
        IsMaximalGaloisFacet k K i D hD hG hi C h6 E := by
  obtain ⟨E, hE, hFE, hmax⟩ := (B).exists_maximal_facet_in_subset
    {H | IsGaloisFacet k K i D hD hG hi C h6 H} F.val F.property
  refine ⟨⟨E, hE⟩, hFE, ?_⟩
  intro H hEH
  exact Subtype.ext (hmax H.val H.property hEH)

/-- Each actual fixed point lies in the combinatorial fixed closure of a
maximal Gamma-facet. -/
theorem exists_maximal_galoisFacet_closure_mem (y : D.ReducedBuilding)
    (hy : IsGaloisFixed k K i D hD y) :
    ∃ E : GaloisFacet k K i D hD hG hi C h6,
      IsMaximalGaloisFacet k K i D hD hG hi C h6 E ∧
        y ∈ galoisFacetClosure k K i D hD hG hi C h6 E := by
  obtain ⟨E, hFE, hmax⟩ := exists_maximal_galoisFacet_above
    k K i D hD hG hi C h6 (galoisFacetAt k K i D hD hG hi C h6 y hy)
  exact ⟨E, hmax, galoisFacetAt k K i D hD hG hi C h6 y hy,
    hFE, (B).mem_buildingFacetAt y, hy⟩

/-- A fixed point and the whole fixed closure of a suitable maximal
Gamma-facet lie in a translated apartment containing its upstairs full facet. -/
theorem exists_maximal_galoisFacet_apartment (y : D.ReducedBuilding)
    (hy : IsGaloisFixed k K i D hD y) :
    ∃ E : GaloisFacet k K i D hD hG hi C h6,
      IsMaximalGaloisFacet k K i D hD hG hi C h6 E ∧
        y ∈ galoisFacetClosure k K i D hD hG hi C h6 E ∧
        ∃ g : rationalPoints (baseChanged k K G),
          E.val.val ⊆ g • (B).apartmentImage ∧
          galoisFacetClosure k K i D hD hG hi C h6 E ⊆ g • (B).apartmentImage := by
  obtain ⟨E, hmax, hyE⟩ := exists_maximal_galoisFacet_closure_mem
    k K i D hD hG hi C h6 y hy
  obtain ⟨g, Ea, _, hEa⟩ := E.val.property
  have hE : E.val.val ⊆ g • (B).apartmentImage := by
    rw [hEa]
    exact (B).translatedApartmentMap_image_subset g Ea
  exact ⟨E, hmax, hyE, g, hE,
    galoisFacetClosure_subset_apartment k K i D hD hG hi C h6 E g hE⟩

/-- Maximal Gamma-facets extend every Gamma-facet and their combinatorial
fixed closures cover the actual fixed set, with translated-apartment containment. -/
def GaloisMaximalFacetsStatement : Prop :=
  (∀ F : GaloisFacet k K i D hD hG hi C h6,
    ∃ E : GaloisFacet k K i D hD hG hi C h6,
      GaloisFacetPrecedes k K i D hD hG hi C h6 F E ∧
        IsMaximalGaloisFacet k K i D hD hG hi C h6 E) ∧
  ∀ y : D.ReducedBuilding, IsGaloisFixed k K i D hD y →
    ∃ E : GaloisFacet k K i D hD hG hi C h6,
      IsMaximalGaloisFacet k K i D hD hG hi C h6 E ∧
        y ∈ galoisFacetClosure k K i D hD hG hi C h6 E ∧
        ∃ g : rationalPoints (baseChanged k K G),
          E.val.val ⊆ g • (B).apartmentImage ∧
          galoisFacetClosure k K i D hD hG hi C h6 E ⊆ g • (B).apartmentImage

theorem galoisMaximalFacets :
    GaloisMaximalFacetsStatement k K i D hD hG hi C h6 :=
  ⟨exists_maximal_galoisFacet_above k K i D hD hG hi C h6,
    exists_maximal_galoisFacet_apartment k K i D hD hG hi C h6⟩

end Langlands.Geometry.Building.KPApartmentData
