import Langlands.AlgebraicGeometry.SchemeLimitSeparatedStatement
import Langlands.AlgebraicGeometry.SchemeLimitRelativeClosedImmersionProof

/-! # Separatedness via the actual base-change diagonal -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

section Diagonal

variable {S X Y T : Scheme.{u}}
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
  (p : T ⟶ S)

include w in
lemma selfPullback_structure :
    pullback.snd f f ≫ a = pullback.fst f f ≫ a := by
  simpa only [Category.assoc, w] using
    congrArg (· ≫ b) (pullback.condition (f := f) (g := f)).symm

/-- Base change preserves the actual self-pullback square. -/
noncomputable def baseChangeDiagonalObjIso :
    pullback p (pullback.fst f f ≫ a) ≅
      pullback.diagonalObj (baseChangeMap a b f w p) :=
  (baseChangeMap_square_isPullback a b f w p (pullback.fst f f ≫ a) a
    (pullback.fst f f) (pullback.snd f f) f rfl
    (selfPullback_structure a b f w) w (IsPullback.of_hasPullback f f)).isoPullback

@[reassoc (attr := simp)]
lemma baseChangeDiagonalObjIso_hom_fst :
    (baseChangeDiagonalObjIso a b f w p).hom ≫ pullback.fst _ _ =
      baseChangeMap (pullback.fst f f ≫ a) a (pullback.fst f f) rfl p :=
  (baseChangeMap_square_isPullback a b f w p (pullback.fst f f ≫ a) a
    (pullback.fst f f) (pullback.snd f f) f rfl
    (selfPullback_structure a b f w) w (IsPullback.of_hasPullback f f)).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma baseChangeDiagonalObjIso_hom_snd :
    (baseChangeDiagonalObjIso a b f w p).hom ≫ pullback.snd _ _ =
      baseChangeMap (pullback.fst f f ≫ a) a (pullback.snd f f)
        (selfPullback_structure a b f w) p :=
  (baseChangeMap_square_isPullback a b f w p (pullback.fst f f ≫ a) a
    (pullback.fst f f) (pullback.snd f f) f rfl
    (selfPullback_structure a b f w) w (IsPullback.of_hasPullback f f)).isoPullback_hom_snd

lemma baseChange_diagonal_comp_iso :
    baseChangeMap a (pullback.fst f f ≫ a) (pullback.diagonal f)
        (by simp) p ≫ (baseChangeDiagonalObjIso a b f w p).hom =
      pullback.diagonal (baseChangeMap a b f w p) := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeDiagonalObjIso_hom_fst]
    apply pullback.hom_ext <;> simp
  · rw [Category.assoc, baseChangeDiagonalObjIso_hom_snd]
    apply pullback.hom_ext <;> simp

lemma isSeparated_baseChangeMap_iff :
    IsSeparated (baseChangeMap a b f w p) ↔
      IsClosedImmersion (baseChangeMap a (pullback.fst f f ≫ a)
        (pullback.diagonal f) (by simp) p) := by
  rw [isSeparated_iff, ← baseChange_diagonal_comp_iso a b f w p,
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]

end Diagonal

/-- Separatedness is detected at one stage by closed-immersion descent
for the actual relative diagonal. -/
theorem relativeSeparatednessDescent : RelativeSeparatednessDescent.{u} := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ c hc p hp
  simpa only [← isSeparated_baseChangeMap_iff a b f w] using
    (relativeClosedImmersionDescent D t a (pullback.fst f f ≫ a)
      (pullback.diagonal f) (by simp) c hc p hp)

end Langlands.AlgebraicGeometry.AffineLimit
