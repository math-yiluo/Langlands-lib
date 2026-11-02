import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionSystem

/-! # Approximation of actions on supplied cartesian systems -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action.CartesianSystem

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ EtaleEquivalenceRelation.{u})
  {F : EtaleEquivalenceRelation.{u}}
  (t : D ⟶ (Functor.const I).obj F)
  (c : Cone D) (m : c.pt ⟶ F)
  (hm : ∀ i, c.π.app i ≫ t.app i = m)
  {P Q : Scheme.{u}} {p : P ⟶ c.pt.U} {q : Q ⟶ F.U}
  {k : P ⟶ Q} (hp : IsPullback k p q m.objMap)

/-- The action-input limit cone for a cartesian relation system. -/
noncomputable def actionCone : Cone
    (TargetLimit.diagram (D ⋙ objectFunctor) (objectComparison D t)
      (pullback.fst F.s q ≫ F.t)) :=
  arrowCone (D ⋙ objectFunctor) m.isCartesian hp (objectComparison D t)
    (objectFunctor.mapCone c).π (object_cone_comparison D t c m hm)

/-- A leg of the action-input cone is the level arrow comparison followed by
its target-base-change identification. -/
lemma actionCone_π_eq (i : I) :
    (actionCone D t c m hm hp).π.app i =
      arrowMap (c.π.app i).isCartesian p (objectMap D t (q := q) i)
        ((objectCone D t c m hm hp).π.app i)
        (objectCone_π_object D t c m hm hp i).symm ≫
      (isPullback_arrowMap_target (t.app i).isCartesian
        (object_isPullback D t (q := q) i)).flip.isoPullback.hom := by
  let l : P ⟶ (objectDiagram D t (q := q)).obj i :=
    (objectCone D t c m hm hp).π.app i
  have hl : l ≫ objectMap D t (q := q) i = p ≫ (c.π.app i).objMap :=
    objectCone_π_object D t c m hm hp i
  have hk : l ≫ (pointComparison D t (q := q)).app i = k :=
    objectCone_π_point D t c m hm hp i
  let v : (Functor.const I).obj c.pt.U ⟶ D ⋙ objectFunctor :=
    (objectFunctor.mapCone c).π
  have hv : ∀ j, v.app j ≫ (objectComparison D t).app j = m.objMap :=
    object_cone_comparison D t c m hm
  let γ : pullback c.pt.s p ⟶
      pullback (t.app i).objMap (pullback.fst F.s q ≫ F.t) :=
    (arrowCone (D ⋙ objectFunctor) m.isCartesian hp (objectComparison D t) v hv).π.app i
  have hγfst : γ ≫ pullback.fst (t.app i).objMap _ =
      (pullback.fst c.pt.s p ≫ c.pt.t) ≫ (c.π.app i).objMap :=
    arrowCone_π_fst (D ⋙ objectFunctor) m.isCartesian hp (objectComparison D t) v hv i
  have hγsnd : γ ≫ pullback.snd (t.app i).objMap _ =
      arrowMap m.isCartesian p q k hp.w.symm :=
    arrowCone_π_snd (D ⋙ objectFunctor) m.isCartesian hp (objectComparison D t) v hv i
  let e : pullback (D.obj i).s (objectMap D t (q := q) i) ≅
      pullback (t.app i).objMap (pullback.fst F.s q ≫ F.t) :=
    (isPullback_arrowMap_target (t.app i).isCartesian
      (object_isPullback D t (q := q) i)).flip.isoPullback
  have hefst : e.hom ≫ pullback.fst (t.app i).objMap _ =
      pullback.fst (D.obj i).s (objectMap D t (q := q) i) ≫ (D.obj i).t :=
    (isPullback_arrowMap_target (t.app i).isCartesian
      (object_isPullback D t (q := q) i)).flip.isoPullback_hom_fst
  have hesnd : e.hom ≫ pullback.snd (t.app i).objMap _ =
      arrowMap (t.app i).isCartesian (objectMap D t (q := q) i) q
        ((pointComparison D t (q := q)).app i)
        (object_isPullback D t (q := q) i).w.symm :=
    (isPullback_arrowMap_target (t.app i).isCartesian
      (object_isPullback D t (q := q) i)).flip.isoPullback_hom_snd
  change γ = arrowMap (c.π.app i).isCartesian p (objectMap D t (q := q) i) l hl.symm ≫ e.hom
  apply pullback.hom_ext
  · rw [hγfst]
    simp only [Category.assoc, hefst, arrowMap_fst_assoc]
    exact congrArg (pullback.fst c.pt.s p ≫ ·) (c.π.app i).isCartesian.1.symm
  · rw [hγsnd, Category.assoc, hesnd]
    apply pullback.hom_ext
    · simp only [Functor.const_obj_obj, Category.assoc, arrowMap_fst,
        arrowMap_fst_assoc]
      rw [← comp_relMap, hm i]
    · simp only [Functor.const_obj_obj, Category.assoc, arrowMap_snd,
        arrowMap_snd_assoc, hk]

/-- A finite target factor lifts to a prospective action compatible with the
original action under the actual object cone leg. -/
lemma targetFactorMap_compatible (i : I) (A : Action c.pt p)
    (b : (TargetLimit.diagram (D ⋙ objectFunctor) (objectComparison D t)
      (pullback.fst F.s q ≫ F.t)).obj i ⟶ Q)
    (hb : b ≫ q = pullback.snd (t.app i).objMap (pullback.fst F.s q ≫ F.t) ≫
      (pullback.fst F.s q ≫ F.t))
    (hfac : (actionCone D t c m hm hp).π.app i ≫ b = A.map ≫ k) :
    A.map ≫ (objectCone D t c m hm hp).π.app i =
      arrowMap (c.π.app i).isCartesian p (objectMap D t (q := q) i)
        ((objectCone D t c m hm hp).π.app i)
        (objectCone_π_object D t c m hm hp i).symm ≫
      targetFactorMap (t.app i).isCartesian (object_isPullback D t (q := q) i) b hb := by
  let l : P ⟶ (objectDiagram D t (q := q)).obj i :=
    (objectCone D t c m hm hp).π.app i
  have hl : l ≫ objectMap D t (q := q) i = p ≫ (c.π.app i).objMap :=
    objectCone_π_object D t c m hm hp i
  have hk : l ≫ (pointComparison D t (q := q)).app i = k :=
    objectCone_π_point D t c m hm hp i
  change A.map ≫ l =
    arrowMap (c.π.app i).isCartesian p (objectMap D t (q := q) i) l hl.symm ≫ _
  apply (object_isPullback D t (q := q) i).hom_ext
  · rw [Category.assoc, hk, Category.assoc, targetFactorMap_comparison,
      ← Category.assoc]
    exact hfac.symm.trans (by rw [actionCone_π_eq])
  · calc
      (A.map ≫ l) ≫ objectMap D t (q := q) i =
          (A.map ≫ p) ≫ (c.π.app i).objMap := by simp only [Category.assoc, hl]
      _ = (pullback.fst c.pt.s p ≫ c.pt.t) ≫ (c.π.app i).objMap := by rw [A.over]
      _ = (arrowMap (c.π.app i).isCartesian p (objectMap D t (q := q) i)
          l hl.symm ≫ targetFactorMap (t.app i).isCartesian
            (object_isPullback D t (q := q) i) b hb) ≫ objectMap D t (q := q) i := by
        simp only [Functor.const_obj_obj, Category.assoc, targetFactorMap_over,
          arrowMap_fst_assoc, (c.π.app i).isCartesian.1]

/-- The prospective action map descends to an actual action domain at one
level of the supplied system. The action laws are not yet asserted. -/
lemma exists_compatible_map_at_level [IsCofiltered I]
    [IsAffine F.U] [IsAffine F.R] [IsAffine Q] [∀ i, IsAffine (D.obj i).U]
    [LocallyOfFinitePresentation q]
    (hc : IsLimit (objectFunctor.mapCone c)) (A : Action c.pt p) :
    ∃ (i : I)
      (b : pullback (D.obj i).s (objectMap D t (q := q) i) ⟶
        (objectDiagram D t (q := q)).obj i),
      b ≫ objectMap D t (q := q) i =
        pullback.fst (D.obj i).s (objectMap D t (q := q) i) ≫ (D.obj i).t ∧
      A.map ≫ (objectCone D t c m hm hp).π.app i =
        arrowMap (c.π.app i).isCartesian p (objectMap D t (q := q) i)
          ((objectCone D t c m hm hp).π.app i)
          (objectCone_π_object D t c m hm hp i).symm ≫ b := by
  have : IsAffineHom F.s := inferInstance
  have (i : I) : IsAffine ((D ⋙ objectFunctor).obj i) :=
    show IsAffine (D.obj i).U from inferInstance
  let v : (Functor.const I).obj c.pt.U ⟶ D ⋙ objectFunctor :=
    (objectFunctor.mapCone c).π
  have hv : ∀ i, v.app i ≫ (objectComparison D t).app i = m.objMap :=
    object_cone_comparison D t c m hm
  obtain ⟨i, b, hfac, hb⟩ := exists_target_factor_at_level (D ⋙ objectFunctor)
    m.isCartesian hp (objectComparison D t) v hv hc A
  exact ⟨i, targetFactorMap (t.app i).isCartesian (object_isPullback D t i) b hb,
    targetFactorMap_over _ _ _ _, targetFactorMap_compatible D t c m hm hp i A b hb hfac⟩

include hm hp in
/-- An action over a finitely presented affine object descends, together
with both cartesian object squares, to a level of a supplied affine system. -/
lemma exists_equivariant_action_at_level [IsCofiltered I]
    [IsAffine F.U] [IsAffine F.R] [IsAffine Q]
    [∀ i, IsAffine (D.obj i).U] [∀ i, IsAffine (D.obj i).R]
    [LocallyOfFinitePresentation q]
    (hc : IsLimit (objectFunctor.mapCone c)) (A : Action c.pt p) :
    ∃ (i : I) (Pi : Scheme.{u}) (pi : Pi ⟶ (D.obj i).U)
      (li : P ⟶ Pi) (ki : Pi ⟶ Q) (B : Action (D.obj i) pi)
      (hi : IsPullback li p pi (c.π.app i).objMap),
      IsPullback ki pi q (t.app i).objMap ∧ li ≫ ki = k ∧
      IsEquivariant (c.π.app i).isCartesian p pi li hi.w.symm A B := by
  obtain ⟨j, b, hb, hw⟩ := exists_compatible_map_at_level D t c m hm hp hc A
  let Qj := (objectDiagram D t (q := q)).obj j
  let qj : Qj ⟶ (D.obj j).U := objectMap D t j
  let kj : Qj ⟶ Q := (pointComparison D t).app j
  let lj : P ⟶ Qj := (objectCone D t c m hm hp).π.app j
  have hpj : IsPullback lj p qj (c.π.app j).objMap :=
    objectCone_isPullback D t c m hm hp j
  have : LocallyOfFinitePresentation qj :=
    MorphismProperty.of_isPullback (object_isPullback D t (q := q) j) inferInstance
  have : IsAffine Qj := inferInstance
  have : IsAffineHom (D.obj j).s := inferInstance
  have : IsAffine (pullback (D.obj j).s qj) := inferInstance
  have : IsAffine (composable (D.obj j) qj) := inferInstance
  let Dj := CartesianDiagram.above D j
  let tj := CartesianDiagram.comparison D j
  let cj := c.whisker (Over.forget j)
  have (a : Over j) : IsAffine (Dj.obj a).U :=
    show IsAffine (D.obj a.left).U from inferInstance
  have hmj : ∀ a, cj.π.app a ≫ tj.app a = c.π.app j := by
    intro a
    exact c.w a.hom
  obtain ⟨a, _, B, hB⟩ := exists_equivariant_action_of_compatible_map
    Dj tj cj (c.π.app j) hmj hpj
    (CartesianDiagram.isLimitObjectAbove D j c hc) A b hb hw (Over.mk (𝟙 j))
  let Pi := (objectDiagram Dj tj (q := qj)).obj a
  let pi : Pi ⟶ (D.obj a.left).U := objectMap Dj tj a
  let li : P ⟶ Pi := (objectCone Dj tj cj (c.π.app j) hmj hpj).π.app a
  let ki : Pi ⟶ Q := (pointComparison Dj tj (q := qj)).app a ≫ kj
  have hi : IsPullback li p pi (c.π.app a.left).objMap :=
    objectCone_isPullback Dj tj cj (c.π.app j) hmj hpj a
  refine ⟨a.left, Pi, pi, li, ki, B, hi, ?_, ?_, hB⟩
  · have H := (object_isPullback Dj tj (q := qj) a).paste_horiz
      (object_isPullback D t (q := q) j)
    have he : (D.map a.hom).objMap ≫ (t.app j).objMap = (t.app a.left).objMap := by
      have Ht := congrArg CartesianMorphism.objMap (t.naturality a.hom)
      simpa only [comp_objMap, Functor.const_obj_obj, Functor.const_obj_map, id_objMap,
        Category.comp_id] using Ht
    change IsPullback ki pi q ((D.map a.hom).objMap ≫ (t.app j).objMap) at H
    simpa only [he] using H
  · change (li ≫ (pointComparison Dj tj (q := qj)).app a) ≫ kj = k
    rw [objectCone_π_point]
    exact objectCone_π_point D t c m hm hp j

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action.CartesianSystem
