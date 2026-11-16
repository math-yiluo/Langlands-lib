import Langlands.AlgebraicGeometry.Picard.PresheafLineBundle

/-! # Naturality of coherent line-bundle transitions -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.PresheafLineBundle

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    (L : PresheafLineBundle F)

/-- Changing the named target family only inserts its equality isomorphism. -/
theorem pullbackIso_target {T U : Over S} (a : T ⟶ U)
    (x : F.obj (op U)) (y : F.obj (op T)) (h : F.map a.op x = y) :
    L.pullbackIso a x y h = L.pullbackIso a x _ rfl ≪≫
      eqToIso (congrArg (L.bundle T) h) := by
  subst y
  simp

/-- A transition may be computed through any specified common restricted family. -/
theorem transition_eq {T U V : Over S} (a : T ⟶ U) (b : T ⟶ V)
    (x : F.obj (op U)) (y : F.obj (op V)) (z : F.obj (op T))
    (ha : F.map a.op x = z) (hb : F.map b.op y = z) :
    L.transition a b x y (ha.trans hb.symm) =
      L.pullbackIso a x z ha ≪≫ (L.pullbackIso b y z hb).symm := by
  rw [L.pullbackIso_target a x z ha, L.pullbackIso_target b y z hb]
  ext
  simp [transition]

/-- Transitions commute with further pullback, using the actual composition
comparisons of line-bundle pullback. -/
theorem transition_precompose {T U V W : Over S} (k : W ⟶ T)
    (a : T ⟶ U) (b : T ⟶ V) (x : F.obj (op U)) (y : F.obj (op V))
    (h : F.map a.op x = F.map b.op y) :
    L.transition (k ≫ a) (k ≫ b) x y
        (by simpa using congrArg (F.map k.op) h) =
      ((LineBundle.pullbackComp k.left a.left).app (L.bundle U x)).symm ≪≫
        (LineBundle.pullback k.left).mapIso (L.transition a b x y h) ≪≫
          (LineBundle.pullbackComp k.left b.left).app (L.bundle V y) := by
  have ha : F.map (k ≫ a).op x = F.map k.op (F.map b.op y) := by
    simpa using congrArg (F.map k.op) h
  have hb : F.map (k ≫ b).op y = F.map k.op (F.map b.op y) := by simp
  rw [L.transition_eq (k ≫ a) (k ≫ b) x y _ ha hb,
    L.transition_eq a b x y _ h rfl,
    L.pullbackIso_comp k a x _ _ h rfl,
    L.pullbackIso_comp k b y _ _ rfl rfl]
  ext
  simp

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The transition is unchanged by a different presentation of the same
structural map on its test scheme. -/
theorem transition_overMk {T : Scheme.{u}} {U V : Over S}
    (a : T ⟶ U.left) (b : T ⟶ V.left)
    (x : F.obj (op U)) (y : F.obj (op V)) (s t : T ⟶ S)
    (has : a ≫ U.hom = s) (hbs : b ≫ V.hom = s)
    (hat : a ≫ U.hom = t) (hbt : b ≫ V.hom = t)
    (hs : F.map (Over.homMk a has : Over.mk s ⟶ U).op x =
      F.map (Over.homMk b hbs : Over.mk s ⟶ V).op y)
    (ht : F.map (Over.homMk a hat : Over.mk t ⟶ U).op x =
      F.map (Over.homMk b hbt : Over.mk t ⟶ V).op y) :
    L.transition (T := Over.mk s) (U := U) (V := V)
        (Over.homMk a has) (Over.homMk b hbs) x y hs =
      L.transition (T := Over.mk t) (U := U) (V := V)
        (Over.homMk a hat) (Over.homMk b hbt) x y ht := by
  have hst : s = t := has.symm.trans hat
  cases hst
  rfl

end Langlands.AlgebraicGeometry.Picard.PresheafLineBundle
