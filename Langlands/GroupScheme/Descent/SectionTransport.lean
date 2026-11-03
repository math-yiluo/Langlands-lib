import Langlands.GroupScheme.Descent.DatumRelation

/-! # Transport of group-valued sections along an actual datum -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

namespace Langlands.GroupScheme.Descent

variable {S T Z : Scheme.{u}}

private def sectionDiagonal (f : T ⟶ S) (r : Z ⟶ T) :
    Over.mk r ⟶ (Over.pullback f).obj (Over.mk (r ≫ f)) :=
  Over.homMk (pullback.lift (𝟙 Z) r (by simp)) (by simp)

private theorem sectionPullback_formula (f : T ⟶ S) (r : Z ⟶ T)
    (H : GroupScheme S) (a : Over.mk (r ≫ f) ⟶ H.X) :
    (Over.mapPullbackAdj f).homEquiv (Over.mk r) H.X a =
      sectionDiagonal f r ≫ (Over.pullback f).map a := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [sectionDiagonal, Over.mapPullbackAdj, Over.pullback_map_left]
  · simp [sectionDiagonal, Over.mapPullbackAdj, Over.pullback_map_left]

/-- The slice pullback adjunction identifies sections as groups. -/
def sectionPullbackEquiv (f : T ⟶ S) (r : Z ⟶ T) (H : GroupScheme S) :
    (Over.mk (r ≫ f) ⟶ H.X) ≃* (Over.mk r ⟶ ((baseChange f).obj H).X) where
  __ := (Over.mapPullbackAdj f).homEquiv (Over.mk r) H.X
  map_mul' a b := by
    change (Over.mapPullbackAdj f).homEquiv (Over.mk r) H.X (a * b) =
      (Over.mapPullbackAdj f).homEquiv (Over.mk r) H.X a *
        (Over.mapPullbackAdj f).homEquiv (Over.mk r) H.X b
    simp only [sectionPullback_formula, Functor.map_mul, MonObj.comp_mul]

/-- The same identification with a specified equal composite. -/
def sectionPullbackEquivOfEq (f : T ⟶ S) (r : Z ⟶ T) (z : Z ⟶ S)
    (h : r ≫ f = z) (H : GroupScheme S) :
    (Over.mk z ⟶ H.X) ≃* (Over.mk r ⟶ ((baseChange f).obj H).X) := by
  subst z
  exact sectionPullbackEquiv f r H

@[simp] theorem sectionPullbackEquivOfEq_apply_left
    (f : T ⟶ S) (r : Z ⟶ T) (z : Z ⟶ S) (h : r ≫ f = z)
    (H : GroupScheme S) (a : Over.mk z ⟶ H.X) :
    (sectionPullbackEquivOfEq f r z h H a).left =
      pullback.lift a.left r (by rw [Over.w a, ← h]; rfl) := by
  subst z
  change ((Over.mapPullbackAdj f).homEquiv (Over.mk r) H.X a).left = _
  rw [sectionPullback_formula]
  apply pullback.hom_ext <;> simp [sectionDiagonal, Over.pullback_map_left]

@[simp] theorem sectionPullbackEquivOfEq_symm_apply_left
    (f : T ⟶ S) (r : Z ⟶ T) (z : Z ⟶ S) (h : r ≫ f = z)
    (H : GroupScheme S) (a : Over.mk r ⟶ ((baseChange f).obj H).X) :
    ((sectionPullbackEquivOfEq f r z h H).symm a).left =
      a.left ≫ pullback.fst H.X.hom f := by
  subst z
  rfl

namespace Datum

variable {B : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

/-- Actual overlap transport acts by a group isomorphism on sections. -/
def sectionTransport (z₁ z₂ : Z ⟶ S) (h : z₁ ≫ p = z₂ ≫ p) :
    (Over.mk z₁ ⟶ G.X) ≃* (Over.mk z₂ ⟶ G.X) := by
  let r := pullback.lift z₁ z₂ h
  let e : ((baseChange (fst p)).obj G).X ≅ ((baseChange (snd p)).obj G).X :=
    (Grp.forget _).mapIso D.overlap
  letI : IsMonHom e.hom := by
    change IsMonHom D.overlap.hom.hom.hom
    infer_instance
  exact (sectionPullbackEquivOfEq (fst p) r z₁ (by simp [r]) G).trans
    ((Hom.mulEquivCongrRight
      (M := ((baseChange (fst p)).obj G).X)
      (N := ((baseChange (snd p)).obj G).X)
      e (Over.mk r)).trans
      (sectionPullbackEquivOfEq (snd p) r z₂ (by simp [r]) G).symm)

/-- The group-theoretic section transport is the earlier actual point transport. -/
theorem sectionTransport_left (z₁ z₂ : Z ⟶ S) (h : z₁ ≫ p = z₂ ≫ p)
    (a : Over.mk z₁ ⟶ G.X) :
    (D.sectionTransport z₁ z₂ h a).left =
      D.move a.left z₂ (by rw [← Category.assoc, Over.w a]; exact h) := by
  simp only [sectionTransport, MulEquiv.trans_apply, Hom.mulEquivCongrRight_apply,
    sectionPullbackEquivOfEq_symm_apply_left]
  dsimp [move, pointOverlap]
  erw [sectionPullbackEquivOfEq_apply_left]
  simp only [Category.assoc, Over.w a]
  rfl

end Datum
end Langlands.GroupScheme.Descent
