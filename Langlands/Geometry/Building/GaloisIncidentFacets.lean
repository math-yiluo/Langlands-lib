import Langlands.Geometry.Building.GaloisFacetCentroids
import Langlands.Geometry.Building.GaloisMaximalFacets
import Langlands.Geometry.Building.IntegerValuationAffineWeylProof

/-! # Coefficient transport and invariant incident facets -/

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
  {v : Valuation K (WithZero (Multiplicative ℤ))}
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

local notation "B" => integerBuildingData D hG hi C h6
local notation "rho" => galoisQuotientAction k K i D hD

include hG hi C h6

local notation "act" => galoisBuildingFacetAction k K i D hD hG hi C h6

omit hG hi C h6 in
/-- The actual coefficient affine map preserves the actual affine-root set. -/
theorem galoisAffineAction_mem_rootStabilizer (σ : K ≃ₐ[k] K) :
    galoisAffineAction k K i D hD σ ∈
      AffineRootSystem.rootStabilizer D.affineRoots := by
  have h : (galoisAffineAction k K i D hD σ)⁻¹ ∈
      AffineRootSystem.rootStabilizer D.affineRoots := by
    intro ψ
    exact galoisAffineFunctional_mem_affineRoots_iff k K i D hD σ ψ
  simpa only [inv_inv] using (AffineRootSystem.rootStabilizer D.affineRoots).inv_mem h

/-- Coefficient transport preserves actual common-apartment face incidence. -/
theorem facetPrecedes_galoisBuildingFacetAction (σ : K ≃ₐ[k] K)
    {F E : (B).BuildingFacet} (hFE : (B).FacetPrecedes F E) :
    (B).FacetPrecedes (act σ F) (act σ E) := by
  obtain ⟨g, Fa, Ea, hface, hF, hE⟩ := hFE
  refine ⟨rationalConjugate k K G σ g,
    galoisAction k K i D hD σ '' Fa, galoisAction k K i D hD σ '' Ea,
    hface.image (galoisAffineAction_mem_rootStabilizer k K i D hD σ), ?_, ?_⟩
  · rw [galoisBuildingFacetAction_val, hF, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro a _
    change rho σ (g • D.apartmentMap a) =
      rationalConjugate k K G σ g • D.apartmentMap (galoisAction k K i D hD σ a)
    rw [galoisQuotientAction_smul, galoisQuotientAction_apartmentMap]
  · rw [galoisBuildingFacetAction_val, hE, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro a _
    change rho σ (g • D.apartmentMap a) =
      rationalConjugate k K G σ g • D.apartmentMap (galoisAction k K i D hD σ a)
    rw [galoisQuotientAction_smul, galoisQuotientAction_apartmentMap]

/-- Invertibility also reflects the same upstairs incidence relation. -/
theorem facetPrecedes_galoisBuildingFacetAction_iff (σ : K ≃ₐ[k] K)
    (F E : (B).BuildingFacet) :
    (B).FacetPrecedes (act σ F) (act σ E) ↔ (B).FacetPrecedes F E := by
  constructor
  · intro h
    have H := facetPrecedes_galoisBuildingFacetAction k K i D hD hG hi C h6 σ⁻¹ h
    simpa only [map_inv, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using H
  · exact facetPrecedes_galoisBuildingFacetAction k K i D hD hG hi C h6 σ

/-- The full combinatorial closure follows the actual coefficient action. -/
theorem image_buildingFacetClosure_galois (σ : K ≃ₐ[k] K) (E : (B).BuildingFacet) :
    rho σ '' (B).buildingFacetClosure E = (B).buildingFacetClosure (act σ E) := by
  have hmap (τ : K ≃ₐ[k] K) (F : (B).BuildingFacet) :
      Set.MapsTo (rho τ) ((B).buildingFacetClosure F)
        ((B).buildingFacetClosure (act τ F)) := by
    rintro y ⟨H, hHF, hy⟩
    exact ⟨act τ H,
      facetPrecedes_galoisBuildingFacetAction k K i D hD hG hi C h6 τ hHF,
      y, hy, rfl⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hmap σ E hy
  · intro y hy
    have H := hmap σ⁻¹ (act σ E) hy
    have H' : (rho σ).symm y ∈ (B).buildingFacetClosure E := by
      simpa only [map_inv, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using H
    exact ⟨(rho σ).symm y, H', (rho σ).apply_symm_apply y⟩

@[simp] theorem galoisBuildingFacetAction_galoisFacet
    (E : GaloisFacet k K i D hD hG hi C h6) (σ : K ≃ₐ[k] K) :
    act σ E.val = E.val :=
  Subtype.ext (image_galoisFacet_eq k K i D hD hG hi C h6 E σ)

/-- Restrict the actual coefficient action to all incident full facets above a
Gamma-facet; the underlying facet and incidence relation are unchanged. -/
def galoisIncidentFacetAction (E : GaloisFacet k K i D hD hG hi C h6) :
    (K ≃ₐ[k] K) →* Equiv.Perm ((B).IncidentFacets E.val) where
  toFun σ := (act σ).subtypeEquiv fun F => by
    simpa only [galoisBuildingFacetAction_galoisFacet] using
      (facetPrecedes_galoisBuildingFacetAction_iff k K i D hD hG hi C h6 σ E.val F).symm
  map_one' := by
    apply Equiv.ext
    intro F
    apply Subtype.ext
    change act 1 F.val = F.val
    simp only [map_one, Equiv.Perm.coe_one, id_eq]
  map_mul' σ τ := by
    apply Equiv.ext
    intro F
    apply Subtype.ext
    change act (σ * τ) F.val = act σ (act τ F.val)
    rw [map_mul]
    rfl

/-- Fixed incident facets are precisely the invariant original full facets. -/
theorem galoisIncidentFacet_fixed_iff
    (E : GaloisFacet k K i D hD hG hi C h6) (F : (B).IncidentFacets E.val) :
    (∀ σ : K ≃ₐ[k] K, galoisIncidentFacetAction k K i D hD hG hi C h6 E σ F = F) ↔
      IsGaloisInvariantFacet k K i D hD hG hi C h6 F.val := by
  constructor
  · intro h σ
    exact congrArg (fun H => H.val.val) (h σ)
  · intro h σ
    exact Subtype.ext (Subtype.ext (h σ))

/-- Maximality is equivalent to having no other invariant incident full facet.
The explicit affine-root-system premise supplies the fixed centroid. -/
theorem isMaximalGaloisFacet_iff_no_other_invariant_incident
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero (B).affineRoots)
    (E : GaloisFacet k K i D hD hG hi C h6) :
    IsMaximalGaloisFacet k K i D hD hG hi C h6 E ↔
      ∀ F : (B).IncidentFacets E.val,
        IsGaloisInvariantFacet k K i D hD hG hi C h6 F.val → F.val = E.val := by
  constructor
  · intro hmax F hF
    have hfixed := (isGaloisFacet_iff_invariant k K i D hD hG hi C h6 hΨ F.val).mpr hF
    exact congrArg Subtype.val (hmax ⟨F.val, hfixed⟩ F.property)
  · intro h F hEF
    exact Subtype.ext (h ⟨F.val, hEF⟩
      (image_galoisFacet_eq k K i D hD hG hi C h6 F))

/-- After the proved integer affine-root-system theorem, an order-one unit is
the only additional input needed for the incident-facet maximality criterion. -/
theorem isMaximalGaloisFacet_iff_no_other_fixed_incident
    (hunit : ∃ t : Kˣ, IntegerValuation.order v t = 1)
    (E : GaloisFacet k K i D hD hG hi C h6) :
    IsMaximalGaloisFacet k K i D hD hG hi C h6 E ↔
      ∀ F : (B).IncidentFacets E.val,
        (∀ σ : K ≃ₐ[k] K, galoisIncidentFacetAction k K i D hD hG hi C h6 E σ F = F) →
          F.val = E.val := by
  rw [isMaximalGaloisFacet_iff_no_other_invariant_incident k K i D hD hG hi C h6
    ((B).isAffineRootSystemWithRankZero_affineRoots hunit)]
  simp only [galoisIncidentFacet_fixed_iff]

/-- Every actual fixed point belongs to the fixed closure of a full facet
having no other invariant incident full facet. -/
theorem exists_maximal_galoisFacet_no_other_invariant
    (hunit : ∃ t : Kˣ, IntegerValuation.order v t = 1)
    (y : D.ReducedBuilding) (hy : IsGaloisFixed k K i D hD y) :
    ∃ E : GaloisFacet k K i D hD hG hi C h6,
      y ∈ galoisFacetClosure k K i D hD hG hi C h6 E ∧
        ∀ F : (B).IncidentFacets E.val,
          IsGaloisInvariantFacet k K i D hD hG hi C h6 F.val → F.val = E.val := by
  obtain ⟨E, hmax, hyE⟩ := exists_maximal_galoisFacet_closure_mem
    k K i D hD hG hi C h6 y hy
  exact ⟨E, hyE,
    (isMaximalGaloisFacet_iff_no_other_invariant_incident k K i D hD hG hi C h6
      ((B).isAffineRootSystemWithRankZero_affineRoots hunit) E).mp hmax⟩

/-- Actual coefficient transport preserves full-facet incidence and closures;
an order-one unit gives the fixed-incident-facet maximality criterion. -/
def GaloisIncidentFacetsStatement : Prop :=
  (∀ (σ : K ≃ₐ[k] K) (F E : (B).BuildingFacet),
    ((B).FacetPrecedes (act σ F) (act σ E) ↔ (B).FacetPrecedes F E) ∧
      rho σ '' (B).buildingFacetClosure E = (B).buildingFacetClosure (act σ E)) ∧
  ∀ (_hunit : ∃ t : Kˣ, IntegerValuation.order v t = 1)
    (E : GaloisFacet k K i D hD hG hi C h6),
    IsMaximalGaloisFacet k K i D hD hG hi C h6 E ↔
      ∀ F : (B).IncidentFacets E.val,
        (∀ σ : K ≃ₐ[k] K, galoisIncidentFacetAction k K i D hD hG hi C h6 E σ F = F) →
          F.val = E.val

theorem galoisIncidentFacets :
    GaloisIncidentFacetsStatement k K i D hD hG hi C h6 := by
  refine ⟨?_, isMaximalGaloisFacet_iff_no_other_fixed_incident k K i D hD hG hi C h6⟩
  intro σ F E
  exact ⟨facetPrecedes_galoisBuildingFacetAction_iff k K i D hD hG hi C h6 σ F E,
    image_buildingFacetClosure_galois k K i D hD hG hi C h6 σ E⟩

end Langlands.Geometry.Building.KPApartmentData
