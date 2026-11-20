import Langlands.AlgebraicGeometry.FiniteOpenFactorization
import Langlands.Geometry.Analytic.AffineAnalytificationConstructibleClosedness
import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismProof
import Langlands.Geometry.Analytic.SchemeAnalytificationOpenGluing
import Mathlib.Topology.Maps.Proper.Basic

/-! # Properness detection for quasi-finite scheme maps -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open _root_.AlgebraicGeometry CategoryTheory Set Topology
open Langlands.AlgebraicGeometry.QuasiFiniteFactorization
open AffineSchemeAnalytification MorphismExistence

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (g : Y ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFiniteType g]

/-- An affine scheme's top chart gives its whole glued analytification. -/
def affineTopChartHomeomorph [IsAffine X] :
    LocalSpace K f ⟨⊤, isAffineOpen_top X⟩ ≃ₜ Space K f :=
  (OpenGluing.isHomeomorph_ι_top K f).homeomorph _

set_option backward.isDefEq.respectTransparency false in
/-- Constructible closedness is detected by the full center preimage of the
analytic space of an affine scheme. -/
theorem isClosed_of_isConstructible_of_isClosed_center_preimage [IsAffine X]
    {s : Set X} (hs : IsConstructible s) (hc : IsClosed (center K f ⁻¹' s)) : IsClosed s := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have : IsAffine (U : Scheme.{u}) := U.property
  have : IsIso (affineOpenMap U) := by
    change IsIso ((U : X.Opens).toScheme.isoSpec.inv ≫ X.topIso.hom)
    infer_instance
  let e := (affineOpenMap U).homeomorph
  apply e.isQuotientMap.isClosed_preimage.mp
  apply AffineAnalytification.isClosed_of_isConstructible_of_isClosed_center_preimage K
    (chartPresentation K f U)
  · exact hs.preimage_of_isOpenEmbedding e.isOpenEmbedding
  · exact hc.preimage (affineTopChartHomeomorph K f).continuous

set_option backward.isDefEq.respectTransparency false in
/-- The glued analytification of a scheme open immersion has image the full
center preimage of the scheme's open image. -/
theorem range_analytification_of_isOpenImmersion (j : X ⟶ Y) (hj : j ≫ g = f)
    [IsOpenImmersion j] :
    Set.range (analytification K f g j hj) = center K g ⁻¹' Set.range j := by
  have hAn := isAnalytificationMap_analytification K f g j hj
  have hcenter := (MorphismCompatibility.compatibility K f g j hj _ hAn).1
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨center K f x, (hcenter x).symm⟩
  · rintro z ⟨x, hx⟩
    obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
    let U' : X.affineOpens := ⟨U, hU⟩
    let V : Y.affineOpens := ⟨j ''ᵁ U, hU.image_of_isOpenImmersion j⟩
    have hUV : U ≤ j ⁻¹ᵁ (V : Y.Opens) := fun x hx => ⟨x, hx, rfl⟩
    have hzV : z ∈ Set.range (ι K g V) := by
      rw [← OpenGluing.range_ι]
      exact ⟨x, hxU, hx⟩
    obtain ⟨v, rfl⟩ := hzV
    have hres : j.resLE (V : Y.Opens) U hUV = (j.isoImage U).hom := by
      apply (cancel_mono (V : Y.Opens).ι).mp
      rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoImage_hom_ι]
    have : IsIso (j.resLE (V : Y.Opens) U hUV) := hres.symm ▸ inferInstance
    let e := AlgEquiv.ofBijective (openCoordinateMap j hj (U := U') (V := V) hUV)
      (ConcreteCategory.bijective_of_isIso (j.resLE (V : Y.Opens) U hUV).appTop)
    let u : LocalSpace K f U' := AffineAnalytification.baseMap K (chartPresentation K f U')
      (chartPresentation K g V) e.symm.toAlgHom v
    refine ⟨ι K f U' u, ?_⟩
    rw [hAn U' V hUV u]
    congr 1
    change AffineAnalytification.baseMap K (chartPresentation K g V) (chartPresentation K f U')
      e.toAlgHom u = v
    exact (AffineAnalytification.MorphismComparison.baseMap_baseMap K (chartPresentation K g V)
      (chartPresentation K f U') (chartPresentation K g V) e.toAlgHom e.symm.toAlgHom
      (AlgHom.id _ _) e.symm_apply_apply v).trans
        (AffineAnalytification.MorphismComparison.baseMap_eq_self K (chartPresentation K g V)
          (AlgHom.id _ _) (fun _ => rfl) v)

set_option backward.isDefEq.respectTransparency false in
/-- A separated, quasi-compact, locally quasi-finite morphism to an affine
scheme is finite if its glued analytification is topologically proper. -/
theorem isFinite_of_isProperMap_analytification (q : X ⟶ Y) (hq : q ≫ g = f)
    [IsAffine Y] [IsSeparated q] [QuasiCompact q] [LocallyOfFiniteType q] [LocallyQuasiFinite q]
    (hproper : IsProperMap (analytification K f g q hq)) : IsFinite q := by
  obtain ⟨D⟩ := nonempty_finiteOpenFactorization q
  let j := D.openMap
  let k := D.finiteMap
  have : IsOpenImmersion j := D.openImmersion
  have : IsFinite k := D.finite
  let t := k ≫ g
  have : LocallyOfFiniteType t := inferInstanceAs (LocallyOfFiniteType (k ≫ g))
  have ht : j ≫ t = f := by rw [← Category.assoc, D.comp_eq, hq]
  let J := analytification K f t j ht
  let H := analytification K t g k rfl
  have hcomp : H.comp J = analytification K f g q hq := by
    apply (existsUnique_isAnalytificationMap K f g q hq).unique ?_
      (isAnalytificationMap_analytification K f g q hq)
    have hm := isAnalytificationMap_comp K f t g j ht k rfl J H
      (isAnalytificationMap_analytification K f t j ht)
      (isAnalytificationMap_analytification K t g k rfl)
    have hjk : j ≫ k = q := D.comp_eq
    simpa only [hjk] using hm
  have : T2Space (Space K t) := (affineTopChartHomeomorph K t).t2Space
  have hJ : IsProperMap J := isProperMap_of_comp_of_t2 J.continuous H.continuous (by
    change IsProperMap (H.comp J)
    rwa [hcomp])
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have hr : IsConstructible (Set.range j) :=
    (isCompact_range j.continuous).isConstructible j.isOpenMap.isOpen_range
  have hclosed : IsClosed (Set.range j) := by
    apply isClosed_of_isConstructible_of_isClosed_center_preimage K t hr
    rw [← range_analytification_of_isOpenImmersion K f t j ht]
    exact hJ.isClosed_range
  have : IsClosedImmersion j := IsClosedImmersion.of_isPreimmersion _ hclosed
  rw [← D.comp_eq]
  infer_instance

end Langlands.Analytic.SchemeAnalytification
