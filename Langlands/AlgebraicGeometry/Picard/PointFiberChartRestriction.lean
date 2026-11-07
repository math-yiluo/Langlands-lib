import Langlands.AlgebraicGeometry.Picard.StackAtlas
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberAtlasRestriction

/-! # Point-fibre representations after restricting the chart along a monomorphism -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory.PseudofunctorPointFiber
open Langlands.CategoryTheory.PseudofunctorPointFiberAtlasRestriction

variable {S X : Scheme.{u}} (f : X ⟶ S) {U V T : Over S}
  (L : LineBundle ((relativeSpace f).obj U)) (M : LineBundle ((relativeSpace f).obj T))

/-- The family restricted along a map of charts. -/
abbrev restrictBundle (j : V ⟶ U) : LineBundle ((relativeSpace f).obj V) :=
  (LineBundle.pullback ((relativeSpace f).map j)).obj L

variable {f L M} {P : Over T.left}
  (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf f L M)

/-- A representation identifies maps into the representing scheme with fibre points. -/
def pointEquiv (Z : Over T.left) : (Z ⟶ P) ≃ PointFiberPoints f L M Z :=
  Equiv.ulift.symm.trans ((e.app (op Z)).toEquiv.trans Equiv.ulift)

/-- The identification is natural in the test scheme. -/
lemma pointEquiv_comp {Z Z' : Over T.left} (q : Z' ⟶ Z) (g : Z ⟶ P) :
    pointEquiv e Z' (q ≫ g) =
      restrict (relative f) (Core.mk L) (Core.mk M) (T.iteratedSliceBackward.map q)
        (pointEquiv e Z g) := by
  have h := ConcreteCategory.congr_hom (e.hom.naturality q.op) (ULift.up g : ULift.{u + 1} (Z ⟶ P))
  exact congrArg ULift.down h

/-- The underlying map from a representing scheme to the chart. -/
def universalMap : P.left ⟶ U.left :=
  (pointEquiv e P (𝟙 P)).1.left

/-- The point classified by a map into the representing scheme has the
composite map to the chart. -/
lemma pointEquiv_fst_left {Z : Over T.left} (g : Z ⟶ P) :
    (pointEquiv e Z g).1.left = g.left ≫ universalMap e := by
  have h := pointEquiv_comp e g (𝟙 P)
  rw [Category.comp_id] at h
  rw [h]
  rfl

variable (j : V ⟶ U)

/-- The part of a representing scheme that maps into the restricted chart. -/
def restrictScheme : Over T.left :=
  Over.mk (pullback.fst (universalMap e) j.left ≫ P.hom)

/-- The inclusion of that part into the representing scheme. -/
def restrictSchemeι : restrictScheme e j ⟶ P :=
  Over.homMk (pullback.fst (universalMap e) j.left) rfl

/-- A restricted point gives a map into the restricted representing scheme. -/
def toRestrictScheme (Z : Over T.left)
    (x : PointFiberPoints f (restrictBundle f L j) M Z) : Z ⟶ restrictScheme e j :=
  let x' : PointFiberPoints f L M Z :=
    mapPoints (relative f) j (Core.mk L) (Core.mk M) (T.iteratedSliceBackward.obj Z) x
  let g : Z ⟶ P := (pointEquiv e Z).symm x'
  Over.homMk (pullback.lift g.left x.1.left (by
    rw [← pointEquiv_fst_left e g]
    simp only [g, Equiv.apply_symm_apply]
    rfl)) (by
    simp only [restrictScheme, Over.mk_hom]
    rw [pullback.lift_fst_assoc]
    exact Over.w g)

@[reassoc (attr := simp)]
lemma toRestrictScheme_left_fst (Z : Over T.left)
    (x : PointFiberPoints f (restrictBundle f L j) M Z) :
    (toRestrictScheme e j Z x).left ≫ pullback.fst (universalMap e) j.left =
      ((pointEquiv e Z).symm (mapPoints (relative f) j (Core.mk L) (Core.mk M)
        (T.iteratedSliceBackward.obj Z) x)).left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma toRestrictScheme_left_snd (Z : Over T.left)
    (x : PointFiberPoints f (restrictBundle f L j) M Z) :
    (toRestrictScheme e j Z x).left ≫ pullback.snd (universalMap e) j.left = x.1.left :=
  pullback.lift_snd _ _ _

lemma toRestrictScheme_comp_ι (Z : Over T.left)
    (x : PointFiberPoints f (restrictBundle f L j) M Z) :
    toRestrictScheme e j Z x ≫ restrictSchemeι e j =
      (pointEquiv e Z).symm (mapPoints (relative f) j (Core.mk L) (Core.mk M)
        (T.iteratedSliceBackward.obj Z) x) := by
  ext1
  rw [Over.comp_left]
  exact toRestrictScheme_left_fst e j Z x

lemma toRestrictScheme_injective [Mono j] (Z : Over T.left) :
    Function.Injective (toRestrictScheme e j Z) := by
  intro x y h
  have h1 := congrArg (· ≫ restrictSchemeι e j) h
  simp only [toRestrictScheme_comp_ι] at h1
  exact mapPoints_injective (relative f) j (Core.mk L) (Core.mk M) _
    ((pointEquiv e Z).symm.injective h1)

/-- A fibre point whose map factors through the restricted chart comes from a
restricted fibre point with the given factorization. -/
lemma exists_mapPoints_eq (Z : Over T.left) (y : PointFiberPoints f L M Z)
    (a : (T.iteratedSliceBackward.obj Z).left ⟶ V) (ha : a ≫ j = y.1) :
    ∃ x : PointFiberPoints f (restrictBundle f L j) M Z,
      mapPoints (relative f) j (Core.mk L) (Core.mk M)
        (T.iteratedSliceBackward.obj Z) x = y ∧ x.1 = a := by
  rcases y with ⟨b, e⟩
  dsimp only at ha
  subst ha
  exact ⟨⟨a, (atlasComparison (relative f) j (Core.mk L) a).symm ≪≫ e⟩,
    by simp [mapPoints], rfl⟩

lemma toRestrictScheme_surjective (Z : Over T.left) :
    Function.Surjective (toRestrictScheme e j Z) := by
  intro h
  let g : Z ⟶ P := h ≫ restrictSchemeι e j
  let y := pointEquiv e Z g
  have hy : y.1.left = (h.left ≫ pullback.snd (universalMap e) j.left) ≫ j.left := by
    rw [pointEquiv_fst_left]
    change (h.left ≫ pullback.fst (universalMap e) j.left) ≫ universalMap e = _
    rw [Category.assoc, pullback.condition, Category.assoc]
  let b : (T.iteratedSliceBackward.obj Z).left ⟶ V :=
    Over.homMk (h.left ≫ pullback.snd (universalMap e) j.left) (by
      have hw := Over.w y.1
      rw [hy] at hw
      rw [← Over.w j]
      simpa only [Category.assoc] using hw)
  have hb : b ≫ j = y.1 := by
    ext1
    rw [Over.comp_left, hy]
    rfl
  obtain ⟨x, hx, hxb⟩ := exists_mapPoints_eq j Z y b hb
  refine ⟨x, ?_⟩
  ext1
  apply pullback.hom_ext
  · rw [toRestrictScheme_left_fst, hx]
    simp [y, g, restrictSchemeι]
  · rw [toRestrictScheme_left_snd, hxb]
    rfl

/-- Restriction of fibre points along a test map corresponds to composition. -/
lemma toRestrictScheme_restrict {Z Z' : Over T.left} (q : Z' ⟶ Z)
    (x : PointFiberPoints f (restrictBundle f L j) M Z) :
    toRestrictScheme e j Z'
        (restrict (relative f) (Core.mk (restrictBundle f L j)) (Core.mk M)
          (T.iteratedSliceBackward.map q) x) =
      q ≫ toRestrictScheme e j Z x := by
  ext1
  apply pullback.hom_ext
  · rw [toRestrictScheme_left_fst]
    erw [mapPoints_restrict (relative f) j (Core.mk L) (Core.mk M)
      (T.iteratedSliceBackward.map q) x]
    have h := pointEquiv_comp e q ((pointEquiv e Z).symm (mapPoints (relative f) j
      (Core.mk L) (Core.mk M) (T.iteratedSliceBackward.obj Z) x))
    rw [Equiv.apply_symm_apply] at h
    rw [← h, Equiv.symm_apply_apply]
    simp
  · rw [toRestrictScheme_left_snd]
    simp
    rfl

/-- The part of a representing scheme over a restricted chart represents the
fibre of the restricted family. -/
def restrictIso [Mono j] :
    (AlgebraicSpace.schemeYoneda T.left).obj (restrictScheme e j) ≅
      pointFiberPresheaf f (restrictBundle f L j) M :=
  (NatIso.ofComponents (fun Z ↦ (Equiv.ulift.trans ((Equiv.ofBijective
      (toRestrictScheme e j Z.unop) ⟨toRestrictScheme_injective e j Z.unop,
        toRestrictScheme_surjective e j Z.unop⟩).trans Equiv.ulift.symm)).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (toRestrictScheme_restrict e j q.unop x.down))).symm

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
