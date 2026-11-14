import Langlands.Geometry.Building.IntegerBuildingFacetCentroids
import Langlands.Geometry.Building.GaloisFixedFacetIncidence

/-! # Canonical fixed centroids of invariant full facets -/

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

/-- Canonical quotient centroids follow the actual semilinear coefficient action. -/
theorem buildingFacetCentroid_galoisBuildingFacetAction
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero (B).affineRoots)
    (σ : K ≃ₐ[k] K) (F : (B).BuildingFacet) :
    (B).buildingFacetCentroid hΨ
        (galoisBuildingFacetAction k K i D hD hG hi C h6 σ F) =
      rho σ ((B).buildingFacetCentroid hΨ F) := by
  let : Fintype (relativeRoots (T := T_K) i_K) := (B).centroidRootFintype
  let : NormedAddCommGroup (TranslationSpace (S := T_K) i_K) :=
    RootTranslationMetric.normedAddCommGroup (S := T_K) i_K
  let : NormedSpace ℝ (TranslationSpace (S := T_K) i_K) :=
    RootTranslationMetric.normedSpace (S := T_K) i_K
  let : FiniteDimensional ℝ (TranslationSpace (S := T_K) i_K) :=
    RootTranslationMetric.finiteDimensional (S := T_K) i_K
  obtain ⟨⟨g, a⟩, hF⟩ := (B).exists_facet_point_presentation F
  have ht : (galoisBuildingFacetAction k K i D hD hG hi C h6 σ F).val =
      (B).translatedApartmentMap (rationalConjugate k K G σ g) ''
        AffineRootSystem.facet (B).affineRoots (galoisAction k K i D hD σ a) := by
    rw [galoisBuildingFacetAction_val, hF]
    change rho σ '' ((fun x => g • D.apartmentMap x) ''
      AffineRootSystem.facet D.affineRoots a) =
        (fun x => rationalConjugate k K G σ g • D.apartmentMap x) ''
          AffineRootSystem.facet D.affineRoots (galoisAction k K i D hD σ a)
    rw [Set.image_image, ← image_facet_galois k K i D hD σ a, Set.image_image]
    apply Set.image_congr
    intro x _
    rw [galoisQuotientAction_smul, galoisQuotientAction_apartmentMap]
  change AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots at hΨ
  have hc : AffineRootSystem.facetCentroid hΨ (galoisAction k K i D hD σ a) =
      galoisAction k K i D hD σ (AffineRootSystem.facetCentroid hΨ a) := by
    have heinv : (galoisAffineAction k K i D hD σ)⁻¹ ∈
        AffineRootSystem.rootStabilizer D.affineRoots := by
      intro ψ
      exact galoisAffineFunctional_mem_affineRoots_iff k K i D hD σ ψ
    have he : galoisAffineAction k K i D hD σ ∈
        AffineRootSystem.rootStabilizer D.affineRoots := by
      simpa only [inv_inv] using (AffineRootSystem.rootStabilizer D.affineRoots).inv_mem heinv
    exact AffineRootSystem.facetCentroid_apply_of_mem_rootStabilizer hΨ he a
  rw [(B).buildingFacetCentroid_eq_of_presentation hΨ _ _ _ ht,
    (B).buildingFacetCentroid_eq_of_presentation hΨ F g a hF,
    hc]
  change rationalConjugate k K G σ g • D.apartmentMap _ =
    rho σ (g • D.apartmentMap _)
  rw [galoisQuotientAction_smul, galoisQuotientAction_apartmentMap]

/-- Invariance means equality of the actual full-facet subsets under every
coefficient permutation. -/
def IsGaloisInvariantFacet (F : (B).BuildingFacet) : Prop :=
  ∀ σ : K ≃ₐ[k] K, rho σ '' F.val = F.val

/-- An invariant full facet has a coefficient-fixed point in its open facet,
namely its canonical centroid. -/
theorem isGaloisFixed_buildingFacetCentroid_of_invariant
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero (B).affineRoots)
    (F : (B).BuildingFacet)
    (hF : IsGaloisInvariantFacet k K i D hD hG hi C h6 F) :
    IsGaloisFixed k K i D hD ((B).buildingFacetCentroid hΨ F) := by
  intro σ
  have he : galoisBuildingFacetAction k K i D hD hG hi C h6 σ F = F :=
    Subtype.ext (hF σ)
  rw [← buildingFacetCentroid_galoisBuildingFacetAction k K i D hD hG hi C h6,
    he]

/-- A full facet meets the coefficient-fixed locus exactly when it is invariant. -/
theorem isGaloisFacet_iff_invariant
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero (B).affineRoots)
    (F : (B).BuildingFacet) :
    IsGaloisFacet k K i D hD hG hi C h6 F ↔
      IsGaloisInvariantFacet k K i D hD hG hi C h6 F := by
  constructor
  · intro hF
    exact image_galoisFacet_eq k K i D hD hG hi C h6 ⟨F, hF⟩
  · intro hF
    exact ⟨(B).buildingFacetCentroid hΨ F, (B).buildingFacetCentroid_mem hΨ F,
      isGaloisFixed_buildingFacetCentroid_of_invariant
        k K i D hD hG hi C h6 hΨ F hF⟩

/-- Fixedness of the canonical centroid detects all invariant full facets. -/
theorem isGaloisFacet_iff_fixed_centroid
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero (B).affineRoots)
    (F : (B).BuildingFacet) :
    IsGaloisFacet k K i D hD hG hi C h6 F ↔
      IsGaloisFixed k K i D hD ((B).buildingFacetCentroid hΨ F) := by
  constructor
  · intro hF
    exact isGaloisFixed_buildingFacetCentroid_of_invariant
      k K i D hD hG hi C h6 hΨ F
      ((isGaloisFacet_iff_invariant k K i D hD hG hi C h6 hΨ F).mp hF)
  · intro hF
    exact ⟨(B).buildingFacetCentroid hΨ F, (B).buildingFacetCentroid_mem hΨ F, hF⟩

/-- The canonical centroid of a Gamma-facet belongs to its actual fixed part. -/
theorem buildingFacetCentroid_mem_galoisFacetFixedPart
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero (B).affineRoots)
    (F : GaloisFacet k K i D hD hG hi C h6) :
    (B).buildingFacetCentroid hΨ F.val ∈
      galoisFacetFixedPart k K i D hD hG hi C h6 F :=
  ⟨(B).buildingFacetCentroid_mem hΨ F.val,
    (isGaloisFacet_iff_fixed_centroid k K i D hD hG hi C h6 hΨ F.val).mp F.property⟩

/-- The original Gamma-facets are precisely the invariant original full facets,
with the same underlying facet. -/
def galoisFacetEquivInvariant
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero (B).affineRoots) :
    GaloisFacet k K i D hD hG hi C h6 ≃
      {F : (B).BuildingFacet // IsGaloisInvariantFacet k K i D hD hG hi C h6 F} where
  toFun F := ⟨F.val,
    (isGaloisFacet_iff_invariant k K i D hD hG hi C h6 hΨ F.val).mp F.property⟩
  invFun F := ⟨F.val,
    (isGaloisFacet_iff_invariant k K i D hD hG hi C h6 hΨ F.val).mpr F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The invariant-facet/fixed-point equivalence is detected by the canonical
centroid, under the explicit affine-root-system premise. -/
def GaloisFacetCentroidsStatement : Prop :=
  ∀ hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero (B).affineRoots,
    ∀ F : (B).BuildingFacet,
      (IsGaloisFacet k K i D hD hG hi C h6 F ↔
        IsGaloisInvariantFacet k K i D hD hG hi C h6 F) ∧
      (IsGaloisFacet k K i D hD hG hi C h6 F ↔
        IsGaloisFixed k K i D hD ((B).buildingFacetCentroid hΨ F))

theorem galoisFacetCentroids :
    GaloisFacetCentroidsStatement k K i D hD hG hi C h6 := by
  intro hΨ F
  exact ⟨isGaloisFacet_iff_invariant k K i D hD hG hi C h6 hΨ F,
    isGaloisFacet_iff_fixed_centroid k K i D hD hG hi C h6 hΨ F⟩

end Langlands.Geometry.Building.KPApartmentData
