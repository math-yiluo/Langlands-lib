import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain
import Mathlib.AlgebraicGeometry.Fiber

/-! # Stalks in a fibre over the smooth locus -/

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

/-- The fibre stalk at a point over the smooth locus of a morphism is reduced. -/
theorem isReduced_fibre_stalk_of_mem_smoothLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (b : Y) (x : f.fiber b) (hx : f.fiberι b x ∈ f.smoothLocus) :
    _root_.IsReduced ((f.fiber b).presheaf.stalk x) := by
  let U := f.smoothLocus
  have hU : Smooth (U.ι ≫ f) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact U.ι_preimage_self
  let V := f.fiberι b ⁻¹ᵁ U
  let fV := V.ι ≫ f.fiberToSpecResidueField b
  have hPull : IsPullback (f.fiberι b ∣_ U) fV (U.ι ≫ f) (Y.fromSpecResidueField b) :=
    (isPullback_morphismRestrict (f.fiberι b) U).paste_vert
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField b))
  have hSmoothV : Smooth fV := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Smooth) hPull hU
  let xV : V := ⟨x, hx⟩
  have : IsRegularLocalRing (V.toScheme.presheaf.stalk xV) :=
    @Smooth.isRegularLocalRing_stalk (Y.residueField b) _ V.toScheme fV hSmoothV xV
  have : IsDomain (V.toScheme.presheaf.stalk xV) := IsRegularLocalRing.isDomain _
  let e := (V.stalkIso xV).symm.commRingCatIsoToRingEquiv
  exact isReduced_of_injective e.toRingHom e.injective

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
