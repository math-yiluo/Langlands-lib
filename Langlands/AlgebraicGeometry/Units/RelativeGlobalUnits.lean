import Langlands.AlgebraicGeometry.Picard.RelativeGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-! # Global units on actual relative schemes -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.RelativeGlobalUnits

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- Units of ordinary global functions on the actual fibre product. -/
abbrev sections (T : Over S) :=
  Γ((Picard.relativeSpace f).obj T, ⊤)ˣ

/-- Restriction is induced by the ordinary pullback of global functions. -/
def restriction {T U : Over S} (h : T ⟶ U) : sections f U →* sections f T :=
  _root_.Units.map ((Picard.relativeSpace f).map h).appTop.hom.toMonoidHom

@[simp]
lemma restriction_val {T U : Over S} (h : T ⟶ U) (a : sections f U) :
    ↑(restriction f h a) =
      ((Picard.relativeSpace f).map h).appTop (a : Γ(_, ⊤)) := rfl

@[simp]
lemma restriction_id (T : Over S) (a : sections f T) :
    restriction f (𝟙 T) a = a := by
  apply _root_.Units.ext
  change ((Picard.relativeSpace f).map (𝟙 T)).appTop (a : Γ(_, ⊤)) = _
  rw [(Picard.relativeSpace f).map_id, Scheme.Hom.id_appTop]
  rfl

@[simp]
lemma restriction_comp {T U V : Over S} (h : T ⟶ U) (j : U ⟶ V)
    (a : sections f V) :
    restriction f (h ≫ j) a = restriction f h (restriction f j a) := by
  apply _root_.Units.ext
  change ((Picard.relativeSpace f).map (h ≫ j)).appTop (a : Γ(_, ⊤)) = _
  rw [(Picard.relativeSpace f).map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- The group-valued presheaf on the entire slice category. -/
def groupPresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (sections f T.unop)
  map h := CommGrpCat.ofHom (restriction f h.unop)
  map_id T := by
    apply CommGrpCat.hom_ext
    exact MonoidHom.ext (restriction_id f T.unop)
  map_comp h j := by
    apply CommGrpCat.hom_ext
    exact MonoidHom.ext (restriction_comp f j.unop h.unop)

/-- The underlying lifted presheaf in the algebraic-space convention. -/
def presheaf : AlgebraicSpace.Presheaf S where
  obj T := ULift.{u + 1} (sections f T.unop)
  map h := ↾fun a => ⟨restriction f h.unop a.down⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.up (restriction_id f T.unop a.down)
  map_comp h j := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.up (restriction_comp f j.unop h.unop a.down)

@[simp]
lemma presheaf_obj (T : Over S) :
    (presheaf f).obj (op T) = ULift.{u + 1} (Γ(pullback T.hom f, ⊤)ˣ) := rfl

@[simp]
lemma presheaf_map_down {T U : Over S} (h : T ⟶ U)
    (a : (presheaf f).obj (op U)) :
    ((presheaf f).map h.op a).down = restriction f h a.down := rfl

/-- A unit on one actual relative scheme induces a map from its scheme Yoneda
presheaf by pulling back that same unit on every test scheme. -/
def fromUniversalUnit (U : Over S) (a : sections f U) :
    (AlgebraicSpace.schemeYoneda S).obj U ⟶ presheaf f where
  app T := ↾fun h => ⟨restriction f h.down a⟩
  naturality {T V} h := by
    ext j
    apply ULift.ext
    exact restriction_comp f h.unop j.down a

@[simp]
lemma fromUniversalUnit_app (U : Over S) (a : sections f U)
    (T : Over S) (h : T ⟶ U) :
    ((fromUniversalUnit f U a).app (op T) ⟨h⟩).down =
      restriction f h a := rfl

/-- Naturality explicitly compares the two ordinary pullbacks of the unit. -/
lemma fromUniversalUnit_naturality (U : Over S) (a : sections f U)
    {T V : Over S} (h : T ⟶ V) (j : V ⟶ U) :
    restriction f h (((fromUniversalUnit f U a).app (op V) ⟨j⟩).down) =
      ((fromUniversalUnit f U a).app (op T) ⟨h ≫ j⟩).down :=
  (restriction_comp f h j a).symm

end Langlands.AlgebraicGeometry.RelativeGlobalUnits
