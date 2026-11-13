import Langlands.Geometry.Building.GaloisFacetAction
import Langlands.Geometry.Building.IntegerBuildingFacetClosure

/-! # Full facets meeting the actual Galois fixed locus -/

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
local notation "rho" => galoisQuotientAction k K i D hD

/-- Fixedness for the actual coefficient action on the original quotient. -/
def IsGaloisFixed (y : D.ReducedBuilding) : Prop :=
  ∀ σ : K ≃ₐ[k] K, rho σ y = y

/-- The fixed subset of the original reduced building. -/
def galoisFixedLocus : Set D.ReducedBuilding :=
  {y | IsGaloisFixed k K i D hD y}

/-- An upstairs full facet meeting the coefficient-fixed subset. -/
def IsGaloisFacet (F : (B).BuildingFacet) : Prop :=
  (F.val ∩ galoisFixedLocus k K i D hD).Nonempty

/-- Gamma-facets keep the original full facet as their underlying object. -/
abbrev GaloisFacet : Type u :=
  {F : (B).BuildingFacet // IsGaloisFacet k K i D hD hG hi C h6 F}

/-- The corresponding facet of the fixed subset, as a subset of the same
upstairs quotient. -/
def galoisFacetFixedPart (F : GaloisFacet k K i D hD hG hi C h6) :
    Set D.ReducedBuilding :=
  F.val.val ∩ galoisFixedLocus k K i D hD

/-- The upstairs facet through a coefficient-fixed point meets the fixed set. -/
def galoisFacetAt (y : D.ReducedBuilding)
    (hy : IsGaloisFixed k K i D hD y) : GaloisFacet k K i D hD hG hi C h6 :=
  ⟨(B).buildingFacetAt y, y, (B).mem_buildingFacetAt y, hy⟩

theorem galoisFacetFixedPart_nonempty
    (F : GaloisFacet k K i D hD hG hi C h6) :
    (galoisFacetFixedPart k K i D hD hG hi C h6 F).Nonempty := F.property

/-- No different full facet can have the same nonempty fixed part. -/
theorem galoisFacetAt_eq_iff_mem (y : D.ReducedBuilding)
    (hy : IsGaloisFixed k K i D hD y)
    (F : GaloisFacet k K i D hD hG hi C h6) :
    galoisFacetAt k K i D hD hG hi C h6 y hy = F ↔
      y ∈ galoisFacetFixedPart k K i D hD hG hi C h6 F := by
  constructor
  · rintro rfl
    exact ⟨(B).mem_buildingFacetAt y, hy⟩
  · intro h
    apply Subtype.ext
    exact ((B).buildingFacetAt_eq_iff_mem y F.val).mpr h.1

theorem existsUnique_galoisFacet_of_fixed (y : D.ReducedBuilding)
    (hy : IsGaloisFixed k K i D hD y) :
    ∃! F : GaloisFacet k K i D hD hG hi C h6,
      y ∈ galoisFacetFixedPart k K i D hD hG hi C h6 F := by
  refine ⟨galoisFacetAt k K i D hD hG hi C h6 y hy,
    ⟨(B).mem_buildingFacetAt y, hy⟩, ?_⟩
  intro F hF
  exact ((galoisFacetAt_eq_iff_mem k K i D hD hG hi C h6 y hy F).mpr hF).symm

theorem galoisFacetFixedPart_injective :
    Function.Injective (galoisFacetFixedPart k K i D hD hG hi C h6) := by
  intro F E hFE
  obtain ⟨y, hy⟩ := galoisFacetFixedPart_nonempty k K i D hD hG hi C h6 F
  have hyE : y ∈ galoisFacetFixedPart k K i D hD hG hi C h6 E := hFE ▸ hy
  exact ((galoisFacetAt_eq_iff_mem k K i D hD hG hi C h6 y hy.2 F).mpr hy).symm.trans
    ((galoisFacetAt_eq_iff_mem k K i D hD hG hi C h6 y hy.2 E).mpr hyE)

/-- Every Gamma-facet is invariant for the actual coefficient action. -/
theorem image_galoisFacet_eq (F : GaloisFacet k K i D hD hG hi C h6)
    (σ : K ≃ₐ[k] K) : rho σ '' F.val.val = F.val.val := by
  obtain ⟨y, hyF, hy⟩ := F.property
  exact (isFacet_image_galoisQuotientAction k K i D hD hG hi C h6 σ
    F.val.property).eq_of_mem_mem (B) F.val.property ⟨y, hyF, hy σ⟩ hyF

/-- Incidence on Gamma-facets is the existing upstairs full-facet relation. -/
def GaloisFacetPrecedes (F E : GaloisFacet k K i D hD hG hi C h6) : Prop :=
  (B).FacetPrecedes F.val E.val

/-- The combinatorial closure in the fixed set, using all its incident lower
Gamma-facets and their fixed parts. -/
def galoisFacetClosure (E : GaloisFacet k K i D hD hG hi C h6) :
    Set D.ReducedBuilding :=
  {y | ∃ F : GaloisFacet k K i D hD hG hi C h6,
    GaloisFacetPrecedes k K i D hD hG hi C h6 F E ∧
      y ∈ galoisFacetFixedPart k K i D hD hG hi C h6 F}

/-- Restricting the original combinatorial closure to the fixed set gives
exactly the union of all incident lower fixed facets. -/
theorem galoisFacetClosure_eq_inter (E : GaloisFacet k K i D hD hG hi C h6) :
    galoisFacetClosure k K i D hD hG hi C h6 E =
      (B).buildingFacetClosure E.val ∩ galoisFixedLocus k K i D hD := by
  apply Set.Subset.antisymm
  · rintro y ⟨F, hFE, hyF, hy⟩
    exact ⟨⟨F.val, hFE, hyF⟩, hy⟩
  · rintro y ⟨hyE, hy⟩
    refine ⟨galoisFacetAt k K i D hD hG hi C h6 y hy, ?_,
      (B).mem_buildingFacetAt y, hy⟩
    exact ((B).mem_buildingFacetClosure_iff_facetPrecedes E.val y).mp hyE

/-- One fixed point in a lower facet and an upper closure determines incidence. -/
theorem galoisFacetPrecedes_iff_nonempty_inter_closure
    (F E : GaloisFacet k K i D hD hG hi C h6) :
    GaloisFacetPrecedes k K i D hD hG hi C h6 F E ↔
      (galoisFacetFixedPart k K i D hD hG hi C h6 F ∩
        galoisFacetClosure k K i D hD hG hi C h6 E).Nonempty := by
  constructor
  · intro hFE
    obtain ⟨y, hy⟩ := galoisFacetFixedPart_nonempty k K i D hD hG hi C h6 F
    exact ⟨y, hy, F, hFE, hy⟩
  · rintro ⟨y, hyF, hyE⟩
    have hyE' := (galoisFacetClosure_eq_inter k K i D hD hG hi C h6 E).subset hyE
    exact ((B).facetPrecedes_iff_nonempty_inter_buildingFacetClosure F.val E.val).mpr
      ⟨y, hyF.1, hyE'.1⟩

/-- Upstairs incidence is detected by containment of the fixed parts in the
combinatorial fixed closure. -/
theorem galoisFacetPrecedes_iff_subset_closure
    (F E : GaloisFacet k K i D hD hG hi C h6) :
    GaloisFacetPrecedes k K i D hD hG hi C h6 F E ↔
      galoisFacetFixedPart k K i D hD hG hi C h6 F ⊆
        galoisFacetClosure k K i D hD hG hi C h6 E := by
  constructor
  · exact fun hFE _ hy => ⟨F, hFE, hy⟩
  · intro hFE
    obtain ⟨y, hy⟩ := galoisFacetFixedPart_nonempty k K i D hD hG hi C h6 F
    exact (galoisFacetPrecedes_iff_nonempty_inter_closure
      k K i D hD hG hi C h6 F E).mpr ⟨y, hy, hFE hy⟩

/-- Fixed combinatorial closures stay in every translated apartment containing
the corresponding upstairs full facet. -/
theorem galoisFacetClosure_subset_apartment
    (E : GaloisFacet k K i D hD hG hi C h6)
    (g : rationalPoints (baseChanged k K G))
    (hE : E.val.val ⊆ g • (B).apartmentImage) :
    galoisFacetClosure k K i D hD hG hi C h6 E ⊆ g • (B).apartmentImage := by
  intro y hy
  exact (B).buildingFacetClosure_subset_apartment E.val g hE
    ((galoisFacetClosure_eq_inter k K i D hD hG hi C h6 E).subset hy).1

/-- The fixed parts partition the fixed set, recover their full facets, and
inherit exactly the upstairs incidence through combinatorial closures. -/
def GaloisFixedFacetIncidenceStatement : Prop :=
  (∀ y : D.ReducedBuilding, IsGaloisFixed k K i D hD y →
    ∃! F : GaloisFacet k K i D hD hG hi C h6,
      y ∈ galoisFacetFixedPart k K i D hD hG hi C h6 F) ∧
  Function.Injective (galoisFacetFixedPart k K i D hD hG hi C h6) ∧
  ∀ E : GaloisFacet k K i D hD hG hi C h6,
    (∀ σ : K ≃ₐ[k] K, rho σ '' E.val.val = E.val.val) ∧
    galoisFacetClosure k K i D hD hG hi C h6 E =
      (B).buildingFacetClosure E.val ∩ galoisFixedLocus k K i D hD ∧
    ∀ F : GaloisFacet k K i D hD hG hi C h6,
      GaloisFacetPrecedes k K i D hD hG hi C h6 F E ↔
        galoisFacetFixedPart k K i D hD hG hi C h6 F ⊆
          galoisFacetClosure k K i D hD hG hi C h6 E

theorem galoisFixedFacetIncidence :
    GaloisFixedFacetIncidenceStatement k K i D hD hG hi C h6 := by
  refine ⟨existsUnique_galoisFacet_of_fixed k K i D hD hG hi C h6,
    galoisFacetFixedPart_injective k K i D hD hG hi C h6, ?_⟩
  intro E
  exact ⟨image_galoisFacet_eq k K i D hD hG hi C h6 E,
    galoisFacetClosure_eq_inter k K i D hD hG hi C h6 E,
    fun F => galoisFacetPrecedes_iff_subset_closure k K i D hD hG hi C h6 F E⟩

end Langlands.Geometry.Building.KPApartmentData
