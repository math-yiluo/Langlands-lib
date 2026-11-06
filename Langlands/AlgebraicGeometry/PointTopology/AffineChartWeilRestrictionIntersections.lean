import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionUniqueness

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- The original affine intersection represents the actual overlap of two
Weil charts whenever that intersection is affine. -/
theorem affineChartWeilRestrictionIntersection_isPullback
    (U V : Y.left.affineOpens) (hUV : IsAffineOpen (U.val ⊓ V.val)) :
    letI : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
    IsPullback
      (affineWeilRestrictionMap A B
        (openOverHomOfLE B Y (inf_le_left : U.val ⊓ V.val ≤ U.val)))
      (affineWeilRestrictionMap A B
        (openOverHomOfLE B Y (inf_le_right : U.val ⊓ V.val ≤ V.val)))
      (affineChartWeilRestrictionι A B Y U) (affineChartWeilRestrictionι A B Y V) := by
  let : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
  let K : Y.left.affineOpens := ⟨U.val ⊓ V.val, hUV⟩
  apply IsPullback.mk'
  · exact (affineChartWeilRestrictionι_naturality A B Y
      (show K ≤ U from (inf_le_left : U.val ⊓ V.val ≤ U.val))).trans
      (affineChartWeilRestrictionι_naturality A B Y
        (show K ≤ V from (inf_le_right : U.val ⊓ V.val ≤ V.val))).symm
  · intro T p q h₁ _h₂
    let : IsOpenImmersion (affineWeilRestrictionMap A B
      (openOverHomOfLE B Y (inf_le_left : U.val ⊓ V.val ≤ U.val))).left :=
        affineWeilRestrictionMap_isOpenImmersion A B _
    apply Over.OverMorphism.ext
    exact (cancel_mono (affineWeilRestrictionMap A B
      (openOverHomOfLE B Y (inf_le_left : U.val ⊓ V.val ≤ U.val))).left).mp
        (congrArg (fun f => f.left) h₁)
  · intro T a b hab
    have hc : affineWeilRestrictionComparison A B (openOver B Y U.val) T a ≫
          openOverι B Y U.val =
        affineWeilRestrictionComparison A B (openOver B Y V.val) T b ≫
          openOverι B Y V.val := by
      rw [← affineChartWeilRestrictionComparison_chart,
        ← affineChartWeilRestrictionComparison_chart, hab]
    exact ⟨affineChartWeilRestrictionIntersectionLift A B Y T U V hUV a b hc,
      affineChartWeilRestrictionIntersectionLift_fst A B Y T U V hUV a b hc,
      affineChartWeilRestrictionIntersectionLift_snd A B Y T U V hUV a b hc⟩

/-- Canonical identification of the original affine-intersection Weil scheme
with the pullback of the two original chart inclusions. -/
def affineChartWeilRestrictionIntersectionIso
    (U V : Y.left.affineOpens) (hUV : IsAffineOpen (U.val ⊓ V.val)) :
    letI : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
    affineWeilRestriction A B (openOver B Y (U.val ⊓ V.val)) ≅
      pullback (affineChartWeilRestrictionι A B Y U)
        (affineChartWeilRestrictionι A B Y V) :=
  (affineChartWeilRestrictionIntersection_isPullback A B Y U V hUV).isoPullback

@[simp]
theorem affineChartWeilRestrictionIntersectionIso_hom_fst
    (U V : Y.left.affineOpens) (hUV : IsAffineOpen (U.val ⊓ V.val)) :
    letI : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
    (affineChartWeilRestrictionIntersectionIso A B Y U V hUV).hom ≫ pullback.fst _ _ =
      affineWeilRestrictionMap A B
        (openOverHomOfLE B Y (inf_le_left : U.val ⊓ V.val ≤ U.val)) :=
  (affineChartWeilRestrictionIntersection_isPullback A B Y U V hUV).isoPullback_hom_fst

@[simp]
theorem affineChartWeilRestrictionIntersectionIso_hom_snd
    (U V : Y.left.affineOpens) (hUV : IsAffineOpen (U.val ⊓ V.val)) :
    letI : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
    (affineChartWeilRestrictionIntersectionIso A B Y U V hUV).hom ≫ pullback.snd _ _ =
      affineWeilRestrictionMap A B
        (openOverHomOfLE B Y (inf_le_right : U.val ⊓ V.val ≤ V.val)) :=
  (affineChartWeilRestrictionIntersection_isPullback A B Y U V hUV).isoPullback_hom_snd

end Langlands.AlgebraicGeometry.PointTopology
