import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Pointed deformations over general test objects -/

noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorPointedDeformations

variable {C : Type u} [Category.{v} C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {T₀ : C} (M : F.obj (.mk (op T₀)))

/-- An actual object over a pointed test with a specified reduction arrow from `M`. -/
abbrev Deformations (T : Under T₀) :=
  StructuredArrow M (F.map T.hom.op.toLoc).toFunctor

/-- The comparison from direct reduction to reduction after restriction. -/
def restrictionComparison {T U : Under T₀} (q : T ⟶ U) :
    (F.map U.hom.op.toLoc).toFunctor ≅
      (F.map q.right.op.toLoc).toFunctor ⋙ (F.map T.hom.op.toLoc).toFunctor :=
  Cat.Hom.toNatIso (F.mapComp' q.right.op.toLoc T.hom.op.toLoc U.hom.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Under.w]))

/-- Pull back the object and retain its reduction arrow through the ordinary comparison. -/
def restrict {T U : Under T₀} (q : T ⟶ U) :
    Deformations F M U ⥤ Deformations F M T :=
  StructuredArrow.map₂ (F := (F.map q.right.op.toLoc).toFunctor) (G := 𝟭 _)
    (𝟙 M) (restrictionComparison F q).hom

@[simp]
lemma restrict_obj_right {T U : Under T₀} (q : T ⟶ U) (A : Deformations F M U) :
    ((restrict F M q).obj A).right = (F.map q.right.op.toLoc).toFunctor.obj A.right :=
  rfl

/-- The specified reduction arrow is retained, rather than replaced by its isomorphism class. -/
lemma restrict_obj_hom {T U : Under T₀} (q : T ⟶ U) (A : Deformations F M U) :
    ((restrict F M q).obj A).hom = A.hom ≫ (restrictionComparison F q).hom.app A.right := by
  simp [restrict, StructuredArrow.map₂]

@[simp]
lemma restrict_map_right {T U : Under T₀} (q : T ⟶ U)
    {A B : Deformations F M U} (a : A ⟶ B) :
    ((restrict F M q).map a).right = (F.map q.right.op.toLoc).toFunctor.map a.right :=
  rfl

/-- Restriction by an identity has the underlying pseudofunctor identity comparison. -/
def restrictIdIso (T : Under T₀) : restrict F M (𝟙 T) ≅ 𝟭 (Deformations F M T) :=
  NatIso.ofComponents (fun A ↦ StructuredArrow.isoMk
    ((Cat.Hom.toNatIso (F.mapId (.mk (op T.right)))).app A.right) (by
      simp only [restrict_obj_hom]
      change (A.hom ≫ (F.mapComp' (𝟙 (.mk (op T.right))) T.hom.op.toLoc
        T.hom.op.toLoc).hom.toNatTrans.app A.right) ≫
        (F.map T.hom.op.toLoc).toFunctor.map
          ((F.mapId (.mk (op T.right))).hom.toNatTrans.app A.right) = A.hom
      simp only [Pseudofunctor.mapComp'_id_comp_hom_app, Category.assoc]
      rw [← Functor.map_comp, ← Cat.Hom₂.comp_app, Iso.inv_hom_id]
      simp)) (by
      intro A B a
      apply StructuredArrow.hom_ext
      exact (Cat.Hom.toNatIso (F.mapId (.mk (op T.right)))).hom.naturality a.right)

/-- Restriction along a composite compares to two successive restrictions. -/
def restrictCompIso {T U V : Under T₀} (q : T ⟶ U) (r : U ⟶ V) :
    restrict F M (q ≫ r) ≅ restrict F M r ⋙ restrict F M q :=
  NatIso.ofComponents (fun A ↦ StructuredArrow.isoMk
    ((Cat.Hom.toNatIso (F.mapComp' r.right.op.toLoc q.right.op.toLoc
      (q ≫ r).right.op.toLoc (by rfl))).app A.right) (by
        simp only [Functor.comp_obj, restrict_obj_hom, restrict_obj_right]
        change (A.hom ≫ (F.mapComp' (q ≫ r).right.op.toLoc T.hom.op.toLoc
          V.hom.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Under.w])).hom.toNatTrans.app A.right) ≫
            (F.map T.hom.op.toLoc).toFunctor.map
              ((F.mapComp' r.right.op.toLoc q.right.op.toLoc
                (q ≫ r).right.op.toLoc (by rfl)).hom.toNatTrans.app A.right) =
          (A.hom ≫ (F.mapComp' r.right.op.toLoc U.hom.op.toLoc
            V.hom.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Under.w])).hom.toNatTrans.app A.right) ≫
              (F.mapComp' q.right.op.toLoc T.hom.op.toLoc
                U.hom.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Under.w])).hom.toNatTrans.app
                  ((F.map r.right.op.toLoc).toFunctor.obj A.right)
        have h := F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app
          r.right.op.toLoc q.right.op.toLoc T.hom.op.toLoc
          (q ≫ r).right.op.toLoc U.hom.op.toLoc V.hom.op.toLoc
          (by rfl) (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Under.w])
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Under.w]) A.right
        simpa only [Category.assoc] using congrArg (fun t ↦ A.hom ≫ t) h)) (by
      intro A B a
      apply StructuredArrow.hom_ext
      exact (Cat.Hom.toNatIso (F.mapComp' r.right.op.toLoc q.right.op.toLoc
        (q ≫ r).right.op.toLoc (by rfl))).hom.naturality a.right)

@[simp]
lemma restrictIdIso_hom_app_right (T : Under T₀) (A : Deformations F M T) :
    ((restrictIdIso F M T).hom.app A).right =
      (F.mapId (.mk (op T.right))).hom.toNatTrans.app A.right := rfl

@[simp]
lemma restrictCompIso_hom_app_right {T U V : Under T₀} (q : T ⟶ U) (r : U ⟶ V)
    (A : Deformations F M V) :
    ((restrictCompIso F M q r).hom.app A).right =
      (F.mapComp r.right.op.toLoc q.right.op.toLoc).hom.toNatTrans.app A.right := by
  change (F.mapComp' r.right.op.toLoc q.right.op.toLoc _ rfl).hom.toNatTrans.app _ = _
  rw [F.mapComp'_eq_mapComp]

@[simp]
lemma restrictCompIso_inv_app_right {T U V : Under T₀} (q : T ⟶ U) (r : U ⟶ V)
    (A : Deformations F M V) :
    ((restrictCompIso F M q r).inv.app A).right =
      (F.mapComp r.right.op.toLoc q.right.op.toLoc).inv.toNatTrans.app A.right := by
  change (F.mapComp' r.right.op.toLoc q.right.op.toLoc _ rfl).inv.toNatTrans.app _ = _
  rw [F.mapComp'_eq_mapComp]

/-- The comparisons retain the pseudofunctor associativity law. -/
lemma restrict_associativity {T U V W : Under T₀}
    (q : T ⟶ U) (r : U ⟶ V) (s : V ⟶ W) :
    (restrictCompIso F M q (r ≫ s)).hom ≫
      Functor.whiskerRight (restrictCompIso F M r s).hom (restrict F M q) ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (restrict F M s) (restrictCompIso F M q r).inv ≫
            (restrictCompIso F M (q ≫ r) s).inv = eqToHom (by simp) := by
  apply NatTrans.ext
  funext A
  apply StructuredArrow.hom_ext
  simp only [NatTrans.comp_app, StructuredArrow.comp_right,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    restrict_map_right, restrictCompIso_hom_app_right,
    restrictCompIso_inv_app_right, restrict_obj_right,
    Functor.associator_hom_app, StructuredArrow.eqToHom_right,
    eqToHom_app, Category.id_comp]
  simp only [Under.comp_right, op_comp, Quiver.Hom.comp_toLoc, restrict_obj_right,
    Functor.comp_obj]
  rw [F.mapComp_assoc_left_hom_app_assoc]
  simp [Strict.associator_eqToIso, PrelaxFunctor.map₂_eqToHom,
    ← reassoc_of% Cat.Hom₂.comp_app]

/-- The identity comparison is compatible with restriction on the source side. -/
lemma restrict_left_unitality {T U : Under T₀} (q : T ⟶ U) :
    (restrictCompIso F M q (𝟙 U)).hom ≫
      Functor.whiskerRight (restrictIdIso F M U).hom (restrict F M q) ≫
        (Functor.leftUnitor _).hom = eqToHom (by simp) := by
  apply NatTrans.ext
  funext A
  apply StructuredArrow.hom_ext
  simp only [NatTrans.comp_app, StructuredArrow.comp_right,
    Functor.whiskerRight_app, restrict_map_right, restrictIdIso_hom_app_right,
    restrictCompIso_hom_app_right, Functor.leftUnitor_hom_app,
    StructuredArrow.eqToHom_right, StructuredArrow.id_right, eqToHom_app]
  simp only [Under.id_right, op_id, Quiver.Hom.id_toLoc, restrict_obj_right,
    Functor.comp_obj]
  rw [F.mapComp_id_left_hom_app]
  simp [Strict.leftUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom,
    ← Functor.map_comp, ← Cat.Hom₂.comp_app]

/-- The identity comparison is compatible with restriction on the target side. -/
lemma restrict_right_unitality {T U : Under T₀} (q : T ⟶ U) :
    (restrictCompIso F M (𝟙 T) q).hom ≫
      Functor.whiskerLeft (restrict F M q) (restrictIdIso F M T).hom ≫
        (Functor.rightUnitor _).hom = eqToHom (by simp) := by
  apply NatTrans.ext
  funext A
  apply StructuredArrow.hom_ext
  simp only [NatTrans.comp_app, StructuredArrow.comp_right,
    Functor.whiskerLeft_app, restrictIdIso_hom_app_right,
    restrictCompIso_hom_app_right, restrict_obj_right, Functor.rightUnitor_hom_app,
    StructuredArrow.eqToHom_right, StructuredArrow.id_right, eqToHom_app]
  simp only [Under.id_right, op_id, Quiver.Hom.id_toLoc, restrict_obj_right,
    Functor.comp_obj]
  rw [F.mapComp_id_right_hom_app]
  simp [Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom,
    ← Cat.Hom₂.comp_app]

/-- The ordinary pseudofunctor of pointed deformations on all tests under `T₀`. -/
def pseudofunctor : LocallyDiscrete (Under T₀)ᵒᵖ ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun T ↦ Cat.of (Deformations F M T.unop))
    (fun q ↦ (restrict F M q.unop).toCatHom)
    (fun T ↦ Cat.Hom.isoMk (restrictIdIso F M T.unop))
    (fun q r ↦ Cat.Hom.isoMk (restrictCompIso F M r.unop q.unop))
    (fun q r s ↦ by
      apply Cat.Hom₂.ext
      simpa only [unop_comp, unop_id, Cat.Hom₂.eqToHom_toNatTrans,
        Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans,
        Cat.whiskerLeft_toNatTrans, Cat.associator_hom_toNatTrans,
        Cat.leftUnitor_hom_toNatTrans, Cat.rightUnitor_hom_toNatTrans,
        Cat.Hom.isoMk, NatTrans.toCatHom₂, Functor.toCatHom] using
        restrict_associativity F M s.unop r.unop q.unop)
    (fun q ↦ by
      apply Cat.Hom₂.ext
      simpa only [unop_comp, unop_id, Cat.Hom₂.eqToHom_toNatTrans,
        Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans,
        Cat.whiskerLeft_toNatTrans, Cat.associator_hom_toNatTrans,
        Cat.leftUnitor_hom_toNatTrans, Cat.rightUnitor_hom_toNatTrans,
        Cat.Hom.isoMk, NatTrans.toCatHom₂, Functor.toCatHom] using
        restrict_left_unitality F M q.unop)
    (fun q ↦ by
      apply Cat.Hom₂.ext
      simpa only [unop_comp, unop_id, Cat.Hom₂.eqToHom_toNatTrans,
        Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans,
        Cat.whiskerLeft_toNatTrans, Cat.associator_hom_toNatTrans,
        Cat.leftUnitor_hom_toNatTrans, Cat.rightUnitor_hom_toNatTrans,
        Cat.Hom.isoMk, NatTrans.toCatHom₂, Functor.toCatHom] using
        restrict_right_unitality F M q.unop)

end Langlands.CategoryTheory.PseudofunctorPointedDeformations
