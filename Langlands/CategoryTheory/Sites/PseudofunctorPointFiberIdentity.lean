import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber
import Langlands.CategoryTheory.Sites.PseudofunctorPointedDeformations

/-! # Points on the identity test and their restrictions -/

noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type u} [Category.{v} C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {U T : C} (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

/-- An ordinary object isomorphism gives a point over the identity test. -/
def identityPoint (a : T ⟶ U) (e : (F.map a.op.toLoc).toFunctor.obj ξ ≅ η) :
    Points F ξ η (Over.mk (𝟙 T)) :=
  ⟨a, e ≪≫ ((Cat.Hom.toNatIso (F.mapId (.mk (op T)))).app η).symm⟩

/-- Restricting that point removes the identity comparison exactly. -/
theorem identityPoint_restrict {T₀ : C} (i : T₀ ⟶ T) (a : T ⟶ U) (p : T₀ ⟶ U)
    (ha : i ≫ a = p) (e : (F.map a.op.toLoc).toFunctor.obj ξ ≅ η) :
    restrict F ξ η (Over.homMk i (Category.comp_id i)) (identityPoint F ξ η a e) =
      (⟨p, (Cat.Hom.toNatIso (F.mapComp' a.op.toLoc i.op.toLoc p.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ha]))).app ξ ≪≫
          (F.map i.op.toLoc).toFunctor.mapIso e⟩ : Points F ξ η (Over.mk i)) := by
  subst p
  dsimp only [restrict]
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  apply Iso.ext
  change
    (F.mapComp' a.op.toLoc i.op.toLoc (i ≫ a).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app ξ ≫
        (F.map i.op.toLoc).toFunctor.map
          (e.hom ≫ (F.mapId (.mk (op T))).inv.toNatTrans.app η) ≫
        (F.mapComp' (𝟙 (.mk (op T))) i.op.toLoc i.op.toLoc).inv.toNatTrans.app η =
      (F.mapComp' a.op.toLoc i.op.toLoc (i ≫ a).op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app ξ ≫
          (F.map i.op.toLoc).toFunctor.map e.hom
  rw [Pseudofunctor.mapComp'_id_comp_inv_app]
  simp [Category.assoc, ← Functor.map_comp, ← Cat.Hom₂.comp_app]

/-- A pointed isomorphism realizes the whole prescribed residue point. -/
theorem exists_identityPoint_of_pointedIso {T₀ : C}
    (M : F.obj (.mk (op T₀))) {A B : Under T₀} (q : A ⟶ B)
    (D : PseudofunctorPointedDeformations.Deformations F M B)
    (N : PseudofunctorPointedDeformations.Deformations F M A)
    [Epi D.hom]
    (e : (PseudofunctorPointedDeformations.restrict F M q).obj D ≅ N)
    (d : (F.map B.hom.op.toLoc).toFunctor.obj D.right ≅
      (F.map A.hom.op.toLoc).toFunctor.obj N.right)
    (hd : D.hom ≫ d.hom = N.hom) :
    ∃ x : Points F D.right N.right (Over.mk (𝟙 A.right)),
      restrict F D.right N.right
        (Over.homMk A.hom (Category.comp_id A.hom)) x =
          (⟨B.hom, d⟩ : Points F D.right N.right (Over.mk A.hom)) := by
  let e' := (StructuredArrow.proj M
    (F.map A.hom.op.toLoc).toFunctor).mapIso e
  refine ⟨identityPoint F D.right N.right q.right e', ?_⟩
  rw [identityPoint_restrict F D.right N.right A.hom q.right B.hom (Under.w q)]
  congr 1
  apply Iso.ext
  apply (cancel_epi D.hom).mp
  have h := StructuredArrow.w e.hom
  rw [PseudofunctorPointedDeformations.restrict_obj_hom] at h
  change D.hom ≫
      ((PseudofunctorPointedDeformations.restrictionComparison F q).hom.app D.right ≫
        (F.map A.hom.op.toLoc).toFunctor.map e.hom.right) = D.hom ≫ d.hom
  simpa only [Category.assoc] using h.trans hd.symm

end Langlands.CategoryTheory.PseudofunctorPointFiber
