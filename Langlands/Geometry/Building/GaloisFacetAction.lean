import Langlands.Geometry.Building.GaloisAffineRootAction
import Langlands.Geometry.Building.IntegerBuildingFacetPartition

/-! # Actual coefficient action on full building facets -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.KPApartmentData

section IntegerData

variable {L : Type u} [Field L]
  {H : GroupScheme (Spec (CommRingCat.of L))} [IsAffineHom H.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of L))}
  {j : S.toGrp ⟶ H} [Mono j.hom.hom.left]
  {v : Valuation L (WithZero (Multiplicative ℤ))}

/-- Bundle supplied apartment, maximal split torus and full V6 data without
changing their apartment or their reduced quotient. -/
def integerBuildingData (D : KPApartmentData j (IntegerValuation.order v))
    (hH : IsConnectedReductive H) (hj : IsMaximalSplitTorus j)
    (C : CentralizerDatum j) (h6 : IntegerValuation.IsOmegaCompatible v D C) :
    IntegerValuationBuildingData v H where
  isConnectedReductive := hH
  S := S
  i := j
  isMaximalSplitTorus := hj
  apartment := D
  centralizer := C
  isOmegaCompatible := h6

end IntegerData

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

section Apartment

variable {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)
  (hD : GaloisStable k K i D)

/-- The actual coefficient action transports the entire sign facet. -/
theorem image_facet_galois (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    galoisAction k K i D hD σ '' AffineRootSystem.facet D.affineRoots x =
      AffineRootSystem.facet D.affineRoots (galoisAction k K i D hD σ x) := by
  simpa only [transportedRoots_galoisAffineAction, galoisAffineAction_apply] using
    AffineRootSystem.image_facet_transportedRoots
      (galoisAffineAction k K i D hD σ) D.affineRoots x

/-- The same coefficient action preserves and reflects full apartment facets. -/
theorem isFacet_image_galois_iff (σ : K ≃ₐ[k] K) (Fa : Set D.Apartment) :
    AffineRootSystem.IsFacet D.affineRoots (galoisAction k K i D hD σ '' Fa) ↔
      AffineRootSystem.IsFacet D.affineRoots Fa :=
  AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq
    (galoisAffineAction k K i D hD σ)
    (transportedRoots_galoisAffineAction k K i D hD σ) Fa

/-- Coefficient transport also identifies the entire weak-sign closure. -/
theorem image_facetClosure_galois (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    galoisAction k K i D hD σ '' AffineRootSystem.facetClosure D.affineRoots x =
      AffineRootSystem.facetClosure D.affineRoots
        (galoisAction k K i D hD σ x) := by
  simpa only [transportedRoots_galoisAffineAction, galoisAffineAction_apply] using
    AffineRootSystem.image_facetClosure_transportedRoots
      (galoisAffineAction k K i D hD σ) D.affineRoots x

/-- Chambers are preserved and reflected for the actual arrangement. -/
theorem isChamber_image_galois_iff (σ : K ≃ₐ[k] K) (Ca : Set D.Apartment) :
    AffineRootSystem.IsChamber D.affineRoots (galoisAction k K i D hD σ '' Ca) ↔
      AffineRootSystem.IsChamber D.affineRoots Ca := by
  simpa only [transportedRoots_galoisAffineAction, galoisAffineAction_apply] using
    AffineRootSystem.isChamber_image_transportedRoots_iff
      (galoisAffineAction k K i D hD σ) D.affineRoots Ca

end Apartment

section Building

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

/-- Actual semilinearity carries every existing full building facet to a facet. -/
theorem isFacet_image_galoisQuotientAction (σ : K ≃ₐ[k] K)
    {Y : Set D.ReducedBuilding} (hY : (integerBuildingData D hG hi C h6).IsFacet Y) :
    (integerBuildingData D hG hi C h6).IsFacet ((galoisQuotientAction k K i D hD) σ '' Y) := by
  obtain ⟨g, Fa, hFa, rfl⟩ := hY
  refine ⟨rationalConjugate k K G σ g, galoisAction k K i D hD σ '' Fa,
    (isFacet_image_galois_iff k K i D hD σ Fa).mpr hFa, ?_⟩
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  change (galoisQuotientAction k K i D hD) σ (g • D.apartmentMap x) =
    rationalConjugate k K G σ g •
      D.apartmentMap (galoisAction k K i D hD σ x)
  rw [galoisQuotientAction_smul, galoisQuotientAction_apartmentMap]

/-- The same transport preserves existing building chambers. -/
theorem isChamber_image_galoisQuotientAction (σ : K ≃ₐ[k] K)
    {Y : Set D.ReducedBuilding} (hY : (integerBuildingData D hG hi C h6).IsChamber Y) :
    (integerBuildingData D hG hi C h6).IsChamber ((galoisQuotientAction k K i D hD) σ '' Y) := by
  obtain ⟨g, Ca, hCa, rfl⟩ := hY
  refine ⟨rationalConjugate k K G σ g, galoisAction k K i D hD σ '' Ca,
    (isChamber_image_galois_iff k K i D hD σ Ca).mpr hCa, ?_⟩
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  change (galoisQuotientAction k K i D hD) σ (g • D.apartmentMap x) =
    rationalConjugate k K G σ g •
      D.apartmentMap (galoisAction k K i D hD σ x)
  rw [galoisQuotientAction_smul, galoisQuotientAction_apartmentMap]

/-- Preservation is an equivalence because the coefficient action is invertible. -/
theorem isFacet_image_galoisQuotientAction_iff (σ : K ≃ₐ[k] K)
    (Y : Set D.ReducedBuilding) :
    (integerBuildingData D hG hi C h6).IsFacet ((galoisQuotientAction k K i D hD) σ '' Y) ↔ (integerBuildingData D hG hi C h6).IsFacet Y := by
  constructor
  · intro hY
    have H := isFacet_image_galoisQuotientAction k K i D hD hG hi C h6 σ⁻¹ hY
    rw [map_inv] at H
    change (integerBuildingData D hG hi C h6).IsFacet
      (((galoisQuotientAction k K i D hD) σ).symm ''
        ((galoisQuotientAction k K i D hD) σ '' Y)) at H
    exact Eq.mp (congrArg (integerBuildingData D hG hi C h6).IsFacet
      (Equiv.symm_image_image ((galoisQuotientAction k K i D hD) σ) Y)) H
  · exact isFacet_image_galoisQuotientAction k K i D hD hG hi C h6 σ

/-- The actual coefficient permutations act on the original full facet subtype. -/
def galoisBuildingFacetAction : (K ≃ₐ[k] K) →* Equiv.Perm (integerBuildingData D hG hi C h6).BuildingFacet where
  toFun σ := ((galoisQuotientAction k K i D hD) σ).setCongr.subtypeEquiv fun Y =>
    (isFacet_image_galoisQuotientAction_iff k K i D hD hG hi C h6 σ Y).symm
  map_one' := by
    apply Equiv.ext
    intro F
    apply Subtype.ext
    change (galoisQuotientAction k K i D hD) 1 '' F.val = F.val
    simp only [map_one, Equiv.Perm.coe_one, Set.image_id]
  map_mul' σ τ := by
    apply Equiv.ext
    intro F
    apply Subtype.ext
    change (galoisQuotientAction k K i D hD) (σ * τ) '' F.val = (galoisQuotientAction k K i D hD) σ '' ((galoisQuotientAction k K i D hD) τ '' F.val)
    rw [map_mul, Set.image_image]
    rfl

@[simp] theorem galoisBuildingFacetAction_val (σ : K ≃ₐ[k] K)
    (F : (integerBuildingData D hG hi C h6).BuildingFacet) :
    (galoisBuildingFacetAction k K i D hD hG hi C h6 σ F).val = (galoisQuotientAction k K i D hD) σ '' F.val := rfl

/-- The full facet through a point follows its coefficient transport. -/
theorem buildingFacetAt_galoisQuotientAction (σ : K ≃ₐ[k] K)
    (y : D.ReducedBuilding) :
    (integerBuildingData D hG hi C h6).buildingFacetAt ((galoisQuotientAction k K i D hD) σ y) =
      galoisBuildingFacetAction k K i D hD hG hi C h6 σ ((integerBuildingData D hG hi C h6).buildingFacetAt y) := by
  apply ((integerBuildingData D hG hi C h6).buildingFacetAt_eq_iff_mem _ _).mpr
  exact Set.mem_image_of_mem _ ((integerBuildingData D hG hi C h6).mem_buildingFacetAt y)

/-- A fixed point's entire full facet is invariant, as a subset of the quotient. -/
theorem image_buildingFacetAt_of_galois_fixed (y : D.ReducedBuilding)
    (hy : ∀ σ : K ≃ₐ[k] K, (galoisQuotientAction k K i D hD) σ y = y) (σ : K ≃ₐ[k] K) :
    (galoisQuotientAction k K i D hD) σ '' ((integerBuildingData D hG hi C h6).buildingFacetAt y).val = ((integerBuildingData D hG hi C h6).buildingFacetAt y).val := by
  have H := congrArg Subtype.val
    (buildingFacetAt_galoisQuotientAction k K i D hD hG hi C h6 σ y)
  simpa only [hy σ, galoisBuildingFacetAction_val] using H.symm

/-- Each coefficient-fixed point lies in a unique invariant full building facet. -/
def GaloisFixedPointFacetStatement : Prop :=
  ∀ y : D.ReducedBuilding,
    (∀ σ : K ≃ₐ[k] K, (galoisQuotientAction k K i D hD) σ y = y) →
    ∃! Y : Set D.ReducedBuilding,
      (integerBuildingData D hG hi C h6).IsFacet Y ∧ y ∈ Y ∧ ∀ σ : K ≃ₐ[k] K, (galoisQuotientAction k K i D hD) σ '' Y = Y

theorem galoisFixedPointFacet :
    GaloisFixedPointFacetStatement k K i D hD hG hi C h6 := by
  intro y hy
  refine ⟨((integerBuildingData D hG hi C h6).buildingFacetAt y).val,
    ⟨((integerBuildingData D hG hi C h6).buildingFacetAt y).property, (integerBuildingData D hG hi C h6).mem_buildingFacetAt y,
      image_buildingFacetAt_of_galois_fixed k K i D hD hG hi C h6 y hy⟩, ?_⟩
  intro Y hY
  exact hY.1.eq_of_mem_mem (integerBuildingData D hG hi C h6) ((integerBuildingData D hG hi C h6).buildingFacetAt y).property hY.2.1
    ((integerBuildingData D hG hi C h6).mem_buildingFacetAt y)

end Building

end Langlands.Geometry.Building.KPApartmentData
