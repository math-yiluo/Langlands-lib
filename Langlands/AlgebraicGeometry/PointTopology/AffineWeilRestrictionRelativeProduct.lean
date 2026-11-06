import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionPullbacks

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable {P X Z : Over (Spec (CommRingCat.of B))}
  [IsAffine P.left] [IsAffine X.left] [IsAffine Z.left]
  [LocallyOfFiniteType P.hom] [LocallyOfFiniteType X.hom]
  [LocallyOfFiniteType Z.hom]

/-- Affine Weil restriction preserves a relative product over the original base,
with the original structural morphisms as the two maps to the smaller base. -/
theorem affineWeilRestrictionMap_relativeIsPullback (i : P ⟶ X) (j : P ⟶ Z)
    (h : IsPullback i.left j.left X.hom Z.hom) :
    IsPullback (affineWeilRestrictionMap A B i).left
      (affineWeilRestrictionMap A B j).left
      (affineWeilRestriction A B X).hom (affineWeilRestriction A B Z).hom := by
  apply IsPullback.mk'
  · exact (Over.w _).trans (Over.w _).symm
  · intro T p q h₁ h₂
    have hpq : p ≫ (affineWeilRestriction A B P).hom =
        q ≫ (affineWeilRestriction A B P).hom := by
      rw [← Over.w (affineWeilRestrictionMap A B i), ← Category.assoc,
        ← Category.assoc, h₁]
    let S := Over.mk (p ≫ (affineWeilRestriction A B P).hom)
    let p' : S ⟶ affineWeilRestriction A B P := Over.homMk p rfl
    let q' : S ⟶ affineWeilRestriction A B P := Over.homMk q hpq.symm
    suffices hpq' : p' = q' from congrArg (fun f => f.left) hpq'
    apply affineWeilRestrictionComparison_injective A B P S
    apply Over.OverMorphism.ext
    apply h.hom_ext
    · have h' : p' ≫ affineWeilRestrictionMap A B i =
          q' ≫ affineWeilRestrictionMap A B i := Over.OverMorphism.ext h₁
      have hc := congrArg (affineWeilRestrictionComparison A B X S) h'
      rw [affineWeilRestrictionComparison_postcomp,
        affineWeilRestrictionComparison_postcomp] at hc
      exact congrArg (fun f => f.left) hc
    · have h' : p' ≫ affineWeilRestrictionMap A B j =
          q' ≫ affineWeilRestrictionMap A B j := Over.OverMorphism.ext h₂
      have hc := congrArg (affineWeilRestrictionComparison A B Z S) h'
      rw [affineWeilRestrictionComparison_postcomp,
        affineWeilRestrictionComparison_postcomp] at hc
      exact congrArg (fun f => f.left) hc
  · intro T a b hab
    let S := Over.mk (a ≫ (affineWeilRestriction A B X).hom)
    let a' : S ⟶ affineWeilRestriction A B X := Over.homMk a rfl
    let b' : S ⟶ affineWeilRestriction A B Z := Over.homMk b hab.symm
    let aB := affineWeilRestrictionComparison A B X S a'
    let bB := affineWeilRestrictionComparison A B Z S b'
    have hw : aB.left ≫ X.hom = bB.left ≫ Z.hom :=
      (Over.w aB).trans (Over.w bB).symm
    let t : ringBaseChange A B S ⟶ P :=
      Over.homMk (h.lift aB.left bB.left hw) (by
        rw [← Over.w i, ← Category.assoc, h.lift_fst]
        exact Over.w aB)
    obtain ⟨r, hr⟩ := affineWeilRestrictionComparison_surjective A B P S t
    refine ⟨r.left, ?_, ?_⟩
    · have h' : r ≫ affineWeilRestrictionMap A B i = a' := by
        apply affineWeilRestrictionComparison_injective A B X S
        rw [affineWeilRestrictionComparison_postcomp, hr]
        apply Over.OverMorphism.ext
        exact h.lift_fst _ _ _
      exact congrArg (fun f => f.left) h'
    · have h' : r ≫ affineWeilRestrictionMap A B j = b' := by
        apply affineWeilRestrictionComparison_injective A B Z S
        rw [affineWeilRestrictionComparison_postcomp, hr]
        apply Over.OverMorphism.ext
        exact h.lift_snd _ _ _
      exact congrArg (fun f => f.left) h'

variable (X Z)

private instance relativeProduct_isAffine :
    IsAffine (Over.mk (pullback.fst X.hom Z.hom ≫ X.hom)).left :=
  inferInstanceAs (IsAffine (pullback X.hom Z.hom))

private instance relativeProduct_locallyOfFiniteType :
    LocallyOfFiniteType (Over.mk (pullback.fst X.hom Z.hom ≫ X.hom)).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom Z.hom ≫ X.hom))

/-- The actual affine Weil restriction of the original relative product is
canonically its relative product over the smaller base. -/
def affineWeilRestrictionRelativeProductIso :
    (affineWeilRestriction A B
      (Over.mk (pullback.fst X.hom Z.hom ≫ X.hom))).left ≅
      pullback (affineWeilRestriction A B X).hom
        (affineWeilRestriction A B Z).hom :=
  (affineWeilRestrictionMap_relativeIsPullback A B
    (Over.homMk (V := X)
      (U := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom))
      (pullback.fst X.hom Z.hom) rfl)
    (Over.homMk (V := Z)
      (U := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom))
      (pullback.snd X.hom Z.hom) pullback.condition.symm)
    (.of_hasPullback X.hom Z.hom)).isoPullback

@[simp]
theorem affineWeilRestrictionRelativeProductIso_hom_fst :
    (affineWeilRestrictionRelativeProductIso A B X Z).hom ≫ pullback.fst _ _ =
      (affineWeilRestrictionMap A B
        (Over.homMk (V := X)
          (U := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom))
          (pullback.fst X.hom Z.hom) rfl)).left :=
  (affineWeilRestrictionMap_relativeIsPullback A B
    (Over.homMk (V := X)
      (U := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom))
      (pullback.fst X.hom Z.hom) rfl)
    (Over.homMk (V := Z)
      (U := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom))
      (pullback.snd X.hom Z.hom) pullback.condition.symm)
    (.of_hasPullback X.hom Z.hom)).isoPullback_hom_fst

@[simp]
theorem affineWeilRestrictionRelativeProductIso_hom_snd :
    (affineWeilRestrictionRelativeProductIso A B X Z).hom ≫ pullback.snd _ _ =
      (affineWeilRestrictionMap A B
        (Over.homMk (V := Z)
          (U := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom))
          (pullback.snd X.hom Z.hom) pullback.condition.symm)).left :=
  (affineWeilRestrictionMap_relativeIsPullback A B
    (Over.homMk (V := X)
      (U := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom))
      (pullback.fst X.hom Z.hom) rfl)
    (Over.homMk (V := Z)
      (U := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom))
      (pullback.snd X.hom Z.hom) pullback.condition.symm)
    (.of_hasPullback X.hom Z.hom)).isoPullback_hom_snd

end Langlands.AlgebraicGeometry.PointTopology
