import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionOpenImmersion

/-! # Actual pullbacks under affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable {W X Y Z : Over (Spec (CommRingCat.of B))}
  [IsAffine W.left] [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
  [LocallyOfFiniteType W.hom] [LocallyOfFiniteType X.hom]
  [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
variable (i : W ⟶ X) (j : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The existing coordinate morphisms take every cartesian square of affine
finite-type schemes to an actual cartesian square over the smaller base. -/
theorem affineWeilRestrictionMap_isPullback (h : IsPullback i j f g) :
    IsPullback (affineWeilRestrictionMap A B i) (affineWeilRestrictionMap A B j)
      (affineWeilRestrictionMap A B f) (affineWeilRestrictionMap A B g) := by
  apply IsPullback.mk'
  · rw [← affineWeilRestrictionMap_comp, ← affineWeilRestrictionMap_comp, h.w]
  · intro T p q h₁ h₂
    apply affineWeilRestrictionComparison_injective A B W T
    apply h.hom_ext
    · exact (affineWeilRestrictionComparison_postcomp A B i T p).symm.trans
        ((congrArg (affineWeilRestrictionComparison A B X T) h₁).trans
          (affineWeilRestrictionComparison_postcomp A B i T q))
    · exact (affineWeilRestrictionComparison_postcomp A B j T p).symm.trans
        ((congrArg (affineWeilRestrictionComparison A B Y T) h₂).trans
          (affineWeilRestrictionComparison_postcomp A B j T q))
  · intro T a b hab
    have hab' : affineWeilRestrictionComparison A B X T a ≫ f =
        affineWeilRestrictionComparison A B Y T b ≫ g :=
      (affineWeilRestrictionComparison_postcomp A B f T a).symm.trans
        ((congrArg (affineWeilRestrictionComparison A B Z T) hab).trans
          (affineWeilRestrictionComparison_postcomp A B g T b))
    let q := h.lift (affineWeilRestrictionComparison A B X T a)
      (affineWeilRestrictionComparison A B Y T b) hab'
    obtain ⟨p, hp⟩ := affineWeilRestrictionComparison_surjective A B W T q
    refine ⟨p, ?_, ?_⟩
    · apply affineWeilRestrictionComparison_injective A B X T
      rw [affineWeilRestrictionComparison_postcomp, hp]
      exact h.lift_fst _ _ _
    · apply affineWeilRestrictionComparison_injective A B Y T
      rw [affineWeilRestrictionComparison_postcomp, hp]
      exact h.lift_snd _ _ _

/-- An explicit actual pullback comparison over `Spec A`, with the existing
coordinate morphisms as its two projections. -/
def affineWeilRestrictionPullbackIso (h : IsPullback i j f g) :
    affineWeilRestriction A B W ≅
      pullback (affineWeilRestrictionMap A B f) (affineWeilRestrictionMap A B g) :=
  (affineWeilRestrictionMap_isPullback A B i j f g h).isoPullback

@[simp]
theorem affineWeilRestrictionPullbackIso_hom_fst (h : IsPullback i j f g) :
    (affineWeilRestrictionPullbackIso A B i j f g h).hom ≫ pullback.fst _ _ =
      affineWeilRestrictionMap A B i :=
  (affineWeilRestrictionMap_isPullback A B i j f g h).isoPullback_hom_fst

@[simp]
theorem affineWeilRestrictionPullbackIso_hom_snd (h : IsPullback i j f g) :
    (affineWeilRestrictionPullbackIso A B i j f g h).hom ≫ pullback.snd _ _ =
      affineWeilRestrictionMap A B j :=
  (affineWeilRestrictionMap_isPullback A B i j f g h).isoPullback_hom_snd

end Langlands.AlgebraicGeometry.PointTopology
