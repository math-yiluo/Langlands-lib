import Langlands.Geometry.Analytic.CompatibleLocalizedGroundFieldExtension
import Langlands.Geometry.Analytic.LocalizedSaturationEquivalence
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-! # The category of analytic spaces with varying ground fields -/

noncomputable section

universe u v

namespace Langlands.Analytic

open _root_.CategoryTheory Opposite CompleteUltrametricField
open scoped Bicategory

private theorem localizedExtend_assoc_inv {K L M N : CompleteUltrametricField.{u}}
    (f : K ⟶ L) (g : L ⟶ M) (h : M ⟶ N)
    (A : K.CompatibleAnalyticCategory.{u, v}) :
    (localizedExtendComp (f ≫ g) h).hom.app A ≫
      (localizedExtend h).map ((localizedExtendComp f g).hom.app A) ≫
      (localizedExtendComp g h).inv.app ((localizedExtend f).obj A) ≫
      (localizedExtendComp f (g ≫ h)).inv.app A =
      eqToHom (congrArg (fun e => (localizedExtend.{u, v} e).obj A) (Category.assoc f g h)) := by
  let t := (localizedExtendComp (f ≫ g) h).hom.app A
  let m := (localizedExtend h).map ((localizedExtendComp f g).hom.app A)
  let a := (localizedExtendComp f (g ≫ h)).app A
  let b := (localizedExtendComp g h).app ((localizedExtend f).obj A)
  let e := eqToHom (congrArg (fun p => (localizedExtend.{u, v} p).obj A) (Category.assoc f g h))
  change t ≫ m ≫ b.inv ≫ a.inv = e
  calc
    _ = (t ≫ m) ≫ b.inv ≫ a.inv := (Category.assoc _ _ _).symm
    _ = (e ≫ a.hom ≫ b.hom) ≫ b.inv ≫ a.inv :=
      congrArg (fun p => p ≫ b.inv ≫ a.inv) (localizedExtend_assoc f g h A)
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension with its analytic unit and tower comparisons, expressed
on the double opposite of the field category for the Grothendieck construction. -/
def scalarExtensionPseudofunctor :
    Pseudofunctor (LocallyDiscrete (CompleteUltrametricField.{u}ᵒᵖ)ᵒᵖ)
      Cat.{max u v + 1, max u v + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun K => Cat.of K.unop.unop.CompatibleAnalyticCategory.{u, v})
    (fun f => (localizedExtend.{u, v} f.unop.unop).toCatHom)
    (fun K => Cat.Hom.isoMk (localizedExtendId.{u, v} K.unop.unop))
    (fun f g => Cat.Hom.isoMk (localizedExtendComp.{u, v} f.unop.unop g.unop.unop))
    (by
      intro K L M N f g h
      apply Cat.Hom₂.ext
      ext A
      simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
        Cat.associator_hom_toNatTrans, Functor.associator_hom_app,
        Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv, NatTrans.toCatHom₂_toNatTrans,
        Functor.toCatHom_toFunctor, Cat.eqToHom_app]
      let t := (localizedExtendComp (f.unop.unop ≫ g.unop.unop) h.unop.unop).hom.app A
      let m := (localizedExtend h.unop.unop).map ((localizedExtendComp f.unop.unop g.unop.unop).hom.app A)
      let r := (localizedExtendComp g.unop.unop h.unop.unop).inv.app ((localizedExtend f.unop.unop).obj A) ≫
        (localizedExtendComp f.unop.unop (g.unop.unop ≫ h.unop.unop)).inv.app A
      change t ≫ m ≫ 𝟙 _ ≫ r = eqToHom _
      exact (congrArg (fun p => t ≫ m ≫ p) (Category.id_comp r)).trans
        (localizedExtend_assoc_inv f.unop.unop g.unop.unop h.unop.unop A))
    (by
      intro K L f
      apply Cat.Hom₂.ext
      ext A
      simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.leftUnitor_hom_toNatTrans,
        Functor.leftUnitor_hom_app, Cat.Hom.isoMk_hom,
        NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor, Cat.eqToHom_app]
      let t := (localizedExtendComp (𝟙 _) f.unop.unop).hom.app A
      let m := (localizedExtend f.unop.unop).map ((localizedExtendId _).hom.app A)
      change t ≫ m ≫ 𝟙 _ = eqToHom _
      exact (congrArg (fun p => t ≫ p) (Category.comp_id m)).trans
        (localizedExtend_id_left f.unop.unop A))
    (by
      intro K L f
      apply Cat.Hom₂.ext
      ext A
      simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.rightUnitor_hom_toNatTrans,
        Functor.rightUnitor_hom_app, Cat.Hom.isoMk_hom,
        NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor, Cat.eqToHom_app]
      let t := (localizedExtendComp f.unop.unop (𝟙 _)).hom.app A
      let m := (localizedExtendId _).hom.app ((localizedExtend f.unop.unop).obj A)
      change t ≫ m ≫ 𝟙 _ = eqToHom _
      exact (congrArg (fun p => t ≫ p) (Category.comp_id m)).trans
        (localizedExtend_id_right f.unop.unop A))

set_option linter.checkUnivs false in
/-- An analytic space together with its complete nonarchimedean ground field.
An arrow points opposite to its ground-field embedding. -/
abbrev SpaceOverField := Pseudofunctor.CoGrothendieck scalarExtensionPseudofunctor.{u, v}

namespace SpaceOverField

/-- The complete ground field of an analytic space. -/
abbrev field (X : SpaceOverField.{u, v}) : CompleteUltrametricField.{u} := X.base.unop

/-- The space in its own analytic category. -/
abbrev space (X : SpaceOverField.{u, v}) : X.field.CompatibleAnalyticCategory.{u, v} :=
  X.fiber

/-- Regard an object of one analytic fibre as a space with a specified field. -/
abbrev withField (K : CompleteUltrametricField.{u}) (X : K.CompatibleAnalyticCategory.{u, v}) :
    SpaceOverField.{u, v} :=
  ⟨op K, X⟩

variable {X Y : SpaceOverField.{u, v}}

/-- The embedding from the target field to the source field. -/
abbrev fieldMap (f : Y ⟶ X) : X.field ⟶ Y.field := f.base.unop

/-- The actual analytic map to the scalar-extended target. -/
abbrev analyticMap (f : Y ⟶ X) : Y.space ⟶ (localizedExtend.{u, v} (fieldMap f)).obj X.space :=
  f.fiber

/-- Form a field-changing analytic arrow from its two components. -/
def homMk (e : X.field ⟶ Y.field)
    (f : Y.space ⟶ (localizedExtend.{u, v} e).obj X.space) : Y ⟶ X :=
  ⟨e.op, f⟩

/-- The field projection is contravariant in isometric field embeddings. -/
def fieldProjection : SpaceOverField.{u, v} ⥤ CompleteUltrametricField.{u}ᵒᵖ :=
  Pseudofunctor.CoGrothendieck.forget _

instance : fieldProjection.{u, v}.IsFibered :=
  inferInstanceAs (Pseudofunctor.CoGrothendieck.forget scalarExtensionPseudofunctor.{u, v}).IsFibered

/-- Scalar extension is the domain of the Cartesian lift of the field arrow. -/
def scalarExtensionArrow (X : SpaceOverField.{u, v}) {L : CompleteUltrametricField.{u}}
    (e : X.field ⟶ L) : withField L ((localizedExtend.{u, v} e).obj X.space) ⟶ X :=
  Pseudofunctor.CoGrothendieck.cartesianLift (F := scalarExtensionPseudofunctor.{u, v}) X.space e.op

/-- The projection from scalar extension has the analytic Cartesian universal property. -/
theorem scalarExtensionArrow_isStronglyCartesian (X : SpaceOverField.{u, v})
    {L : CompleteUltrametricField.{u}} (e : X.field ⟶ L) :
    fieldProjection.IsStronglyCartesian e.op (scalarExtensionArrow X e) :=
  Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := scalarExtensionPseudofunctor.{u, v}) X.space e.op

/-- The fibre over a fixed field, in the compatible presentation model,
is equivalent to the localized saturated analytic category. -/
def fixedFieldEquivalence (K : CompleteUltrametricField.{u}) :
    Functor.Fiber fieldProjection.{u, v} (op K) ≌
      SaturatedAtlasPresentation.LocalizedCategory.{u, max u v, max u v} (K := K.carrier) :=
  (Functor.Fiber.inducedFunctor (Pseudofunctor.CoGrothendieck.comp_const
    scalarExtensionPseudofunctor.{u, v} (op K))).asEquivalence.symm.trans
      CompatibleAtlasPresentation.localizedSaturationEquivalence

end SpaceOverField

end Langlands.Analytic
