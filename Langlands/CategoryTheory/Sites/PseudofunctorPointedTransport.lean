import Langlands.CategoryTheory.Sites.PseudofunctorPointedDeformations

/-! # Transport of pointings and composite restrictions of pointed deformations -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

namespace Langlands.CategoryTheory.PseudofunctorPointedTransport

open PseudofunctorPointedDeformations

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {T₀ : C} (M : F.obj (.mk (op T₀)))

section Transport

variable {V W : Under T₀} (s : V ⟶ W) (Z : F.obj (.mk (op W.right)))
  (ξ : Deformations F M V) (e : (F.map s.right.op.toLoc).toFunctor.obj Z ≅ ξ.right)

/-- The deformation over `W` with underlying object `Z`, pointed so that its restriction
along `s` is identified with `ξ` through `e`. -/
abbrev transport : Deformations F M W :=
  StructuredArrow.mk (ξ.hom ≫ (F.map V.hom.op.toLoc).toFunctor.map e.inv ≫
    (restrictionComparison F s).inv.app Z)

@[simp]
lemma transport_right : (transport F M s Z ξ e).right = Z := rfl

lemma transport_hom : (transport F M s Z ξ e).hom = ξ.hom ≫
    (F.map V.hom.op.toLoc).toFunctor.map e.inv ≫ (restrictionComparison F s).inv.app Z := rfl

/-- The restriction of the transported deformation is the given one. -/
def transportIso : (restrict F M s).obj (transport F M s Z ξ e) ≅ ξ :=
  StructuredArrow.isoMk e (by
    rw [restrict_obj_hom]
    change ((ξ.hom ≫ (F.map V.hom.op.toLoc).toFunctor.map e.inv ≫
      (restrictionComparison F s).inv.app Z) ≫ (restrictionComparison F s).hom.app Z) ≫
        (F.map V.hom.op.toLoc).toFunctor.map e.hom = ξ.hom
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id])

end Transport

/-- Restriction along a composite, with the composite named and the two successive
restrictions written as nested objects. -/
def restrictCompObjIso {T U V : Under T₀} (q : T ⟶ U) (r : U ⟶ V) (qr : T ⟶ V)
    (h : q ≫ r = qr) (A : Deformations F M V) :
    (restrict F M q).obj ((restrict F M r).obj A) ≅ (restrict F M qr).obj A :=
  ((restrictCompIso F M q r).app A).symm ≪≫
    eqToIso (congrArg (fun t ↦ (restrict F M t).obj A) h)

/-- A pointed deformation whose restriction along a composite `q ≫ r` is `ξ` gives a
pointed deformation over the middle test whose restriction along `q` is `ξ`. -/
lemma exists_restrict_of_comp {T U V : Under T₀} (q : T ⟶ U) (r : U ⟶ V) (qr : T ⟶ V)
    (h : q ≫ r = qr) (A : Deformations F M V) (ξ : Deformations F M T)
    (e : (restrict F M qr).obj A ≅ ξ) :
    ∃ B : Deformations F M U, Nonempty ((restrict F M q).obj B ≅ ξ) :=
  ⟨(restrict F M r).obj A, ⟨restrictCompObjIso F M q r qr h A ≪≫ e⟩⟩

end Langlands.CategoryTheory.PseudofunctorPointedTransport
