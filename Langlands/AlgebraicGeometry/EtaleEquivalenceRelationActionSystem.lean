import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionLimits
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianDiagram

/-! # Eventual actions in cartesian relation diagrams -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

namespace CartesianSystem

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ EtaleEquivalenceRelation.{u})
  {F : EtaleEquivalenceRelation.{u}}
  (t : D ⟶ (Functor.const I).obj F)

/-- The object component of a comparison to a fixed relation. -/
@[simps]
def objectComparison : D ⋙ objectFunctor ⟶ (Functor.const I).obj F.U where
  app i := (t.app i).objMap
  naturality i j a := by
    have H := congrArg CartesianMorphism.objMap (t.naturality a)
    simpa only [comp_objMap, Functor.const_obj_map, id_objMap,
      Functor.comp_map, objectFunctor_map, Functor.const_obj_obj] using H

variable (c : Cone D) (m : c.pt ⟶ F)
  (hm : ∀ i, c.π.app i ≫ t.app i = m)

include hm in
lemma object_cone_comparison (i : I) :
    (objectFunctor.mapCone c).π.app i ≫ (objectComparison D t).app i = m.objMap :=
  congrArg CartesianMorphism.objMap (hm i)

variable {P Q : Scheme.{u}} {p : P ⟶ c.pt.U} {q : Q ⟶ F.U}
  {k : P ⟶ Q} (hp : IsPullback k p q m.objMap)

/-- Pulling back a fixed object gives the object diagram for law descent. -/
noncomputable def objectDiagram : I ⥤ Scheme.{u} :=
  TargetLimit.diagram (D ⋙ objectFunctor) (objectComparison D t) q

instance [IsAffine F.U] [IsAffine Q] [∀ i, IsAffine (D.obj i).U] (i : I) :
    IsAffine ((objectDiagram D t (q := q)).obj i) := by
  change IsAffine (pullback (t.app i).objMap q)
  have : IsAffineHom q := inferInstance
  infer_instance

/-- Structural map of a pulled-back object to its relation's object scheme. -/
noncomputable def objectMap (i : I) :
    (objectDiagram D t (q := q)).obj i ⟶ (D.obj i).U :=
  pullback.fst (t.app i).objMap q

/-- Object comparison back to the fixed object. -/
noncomputable def pointComparison : objectDiagram D t (q := q) ⟶
    (Functor.const I).obj Q :=
  TargetLimit.comparison (D ⋙ objectFunctor) (objectComparison D t) q

lemma object_isPullback (i : I) :
    IsPullback ((pointComparison D t (q := q)).app i) (objectMap D t (q := q) i)
      q (t.app i).objMap :=
  (IsPullback.of_hasPullback (t.app i).objMap q).flip

/-- The supplied upper object is the point of the object cone. -/
noncomputable def objectCone : Cone (objectDiagram D t (q := q)) :=
  TargetLimit.coneOfPullback (D ⋙ objectFunctor) (objectComparison D t) q
    (objectFunctor.mapCone c) m.objMap (object_cone_comparison D t c m hm) hp.flip

@[reassoc (attr := simp)]
lemma objectCone_π_object (i : I) :
    (objectCone D t c m hm hp).π.app i ≫ objectMap D t (q := q) i =
      p ≫ (c.π.app i).objMap :=
  TargetLimit.coneOfPullback_π_fst _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma objectCone_π_point (i : I) :
    (objectCone D t c m hm hp).π.app i ≫ (pointComparison D t (q := q)).app i = k :=
  TargetLimit.coneOfPullback_π_snd _ _ _ _ _ _ _ _

/-- Each upper-to-level object square is cartesian. -/
lemma objectCone_isPullback (i : I) :
    IsPullback ((objectCone D t c m hm hp).π.app i) p
      (objectMap D t (q := q) i) (c.π.app i).objMap := by
  have H : IsPullback
      ((objectCone D t c m hm hp).π.app i ≫ (pointComparison D t (q := q)).app i)
      p q ((c.π.app i).objMap ≫ (t.app i).objMap) := by
    rw [objectCone_π_point, ← comp_objMap, hm i]
    exact hp
  exact H.of_right (objectCone_π_object D t c m hm hp i)
    (object_isPullback D t (q := q) i)

/-- The supplied upper composable domain is the point of the law cone. -/
noncomputable def composableCone : Cone
    (TargetLimit.diagram (D ⋙ objectFunctor) (objectComparison D t)
      (outerArrow F q ≫ F.t)) :=
  TargetLimit.coneOfPullback (D ⋙ objectFunctor) (objectComparison D t)
    (outerArrow F q ≫ F.t) (objectFunctor.mapCone c) m.objMap
    (object_cone_comparison D t c m hm)
    (isPullback_composableMap_target m.isCartesian hp).flip

include hm in
/-- A prospective map compatible with a genuine action acquires its two action
laws at a level of a supplied affine cofiltered object limit. -/
lemma exists_action_of_compatible_map [IsCofiltered I]
    [IsAffine F.U] [IsAffine Q] [IsAffine (composable F q)]
    [∀ i, IsAffine (D.obj i).U] [LocallyOfFiniteType q]
    (hc : IsLimit (objectFunctor.mapCone c))
    (A : Action c.pt p)
    (b : pullback F.s q ⟶ Q) (hb : b ≫ q = pullback.fst F.s q ≫ F.t)
    (hw : A.map ≫ k = arrowMap m.isCartesian p q k hp.w.symm ≫ b)
    (i : I) :
    ∃ (j : I) (_ : j ⟶ i)
      (B : Action (D.obj j) (objectMap D t (q := q) j)),
      B.map ≫ (pointComparison D t (q := q)).app j =
        arrowMap (t.app j).isCartesian (objectMap D t (q := q) j) q
          ((pointComparison D t (q := q)).app j)
          (object_isPullback D t (q := q) j).w.symm ≫ b := by
  let DU := D ⋙ objectFunctor
  let v := pointComparison D t (q := q)
  let C := TargetLimit.diagram DU (objectComparison D t) (outerArrow F q ≫ F.t)
  let z := TargetLimit.comparison DU (objectComparison D t) (outerArrow F q ≫ F.t)
  let cD := objectCone D t c m hm hp
  let cC := composableCone D t c m hm hp
  have (j : I) : IsAffine (C.obj j) := by
    change IsAffine (pullback (t.app j).objMap (outerArrow F q ≫ F.t))
    have : IsAffineHom (outerArrow F q ≫ F.t) := inferInstance
    infer_instance
  have hcD : IsLimit cD :=
    TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ hp.flip hc
  have hcC : IsLimit cC :=
    TargetLimit.isLimitConeOfPullback _ _ _ _ _ _
      (isPullback_composableMap_target m.isCartesian hp).flip hc
  have hu : cD.π.app i ≫ v.app i ≫ unitInput q ≫ b = cD.π.app i ≫ v.app i := by
    have H := unit_equation_naturality A.map b hw
    simpa only [cD, objectCone, v, pointComparison, TargetLimit.comparison,
      TargetLimit.coneOfPullback_π_snd_assoc, TargetLimit.coneOfPullback_π_snd,
      unitInput, A.unital, Category.id_comp] using H.symm
  have ha : cC.π.app i ≫ z.app i ≫ successive b hb =
      cC.π.app i ≫ z.app i ≫ composite b := by
    have H := congrArg (· ≫ k) (associative_universal A)
    rw [successive_naturality A.map A.over b hb hw,
      composite_naturality A.map b hw] at H
    simpa only [cC, composableCone, z, TargetLimit.comparison,
      TargetLimit.coneOfPullback_π_snd_assoc] using H
  exact exists_action_at_level q (objectDiagram D t (q := q)) C v z
    cD hcD cC hcC (fun j => D.obj j) (objectMap D t (q := q))
    (fun j => (t.app j).objMap) (fun j => (t.app j).relMap)
    (fun j => (t.app j).isCartesian) (object_isPullback D t (q := q))
    (fun j => (isPullback_composableMap_target (t.app j).isCartesian
      (object_isPullback D t (q := q) j)).flip.isoPullback)
    (fun j => (isPullback_composableMap_target (t.app j).isCartesian
      (object_isPullback D t (q := q) j)).flip.isoPullback_hom_snd)
    b hb i hu ha

include hm in
/-- The action produced at a later level is equivariant with the original
action under the actual cone leg. -/
lemma exists_equivariant_action_of_compatible_map [IsCofiltered I]
    [IsAffine F.U] [IsAffine Q] [IsAffine (composable F q)]
    [∀ i, IsAffine (D.obj i).U] [LocallyOfFiniteType q]
    (hc : IsLimit (objectFunctor.mapCone c))
    (A : Action c.pt p)
    (b : pullback F.s q ⟶ Q) (hb : b ≫ q = pullback.fst F.s q ≫ F.t)
    (hw : A.map ≫ k = arrowMap m.isCartesian p q k hp.w.symm ≫ b)
    (i : I) :
    ∃ (j : I) (_ : j ⟶ i)
      (B : Action (D.obj j) (objectMap D t (q := q) j)),
      IsEquivariant (c.π.app j).isCartesian p (objectMap D t (q := q) j)
        ((objectCone D t c m hm hp).π.app j)
        (objectCone_π_object D t c m hm hp j).symm A B := by
  obtain ⟨j, a, B, hB⟩ :=
    exists_action_of_compatible_map D t c m hm hp hc A b hb hw i
  refine ⟨j, a, B, ?_⟩
  let l : P ⟶ (objectDiagram D t (q := q)).obj j :=
    (objectCone D t c m hm hp).π.app j
  have hl : l ≫ objectMap D t (q := q) j = p ≫ (c.π.app j).objMap :=
    objectCone_π_object D t c m hm hp j
  have hk : l ≫ (pointComparison D t (q := q)).app j = k :=
    objectCone_π_point D t c m hm hp j
  change A.map ≫ l =
    arrowMap (c.π.app j).isCartesian p (objectMap D t (q := q) j) l hl.symm ≫ B.map
  apply (object_isPullback D t (q := q) j).hom_ext
  · rw [Category.assoc, hk,
      Category.assoc, hB, ← Category.assoc, hw]
    apply congrArg (· ≫ b)
    apply pullback.hom_ext
    · simp only [Functor.const_obj_obj, Category.assoc, arrowMap_fst,
        arrowMap_fst_assoc]
      rw [← comp_relMap, hm j]
    · simp only [Functor.const_obj_obj, Category.assoc, arrowMap_snd, arrowMap_snd_assoc,
        hk]
  · calc
      (A.map ≫ l) ≫ objectMap D t (q := q) j =
          (A.map ≫ p) ≫ (c.π.app j).objMap := by simp only [Category.assoc, hl]
      _ = (pullback.fst c.pt.s p ≫ c.pt.t) ≫ (c.π.app j).objMap := by rw [A.over]
      _ = (arrowMap (c.π.app j).isCartesian p (objectMap D t (q := q) j)
          l hl.symm ≫ B.map) ≫ objectMap D t (q := q) j := by
        simp only [Functor.const_obj_obj, Category.assoc, B.over, arrowMap_fst_assoc,
          (c.π.app j).isCartesian.1]

end CartesianSystem

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action
