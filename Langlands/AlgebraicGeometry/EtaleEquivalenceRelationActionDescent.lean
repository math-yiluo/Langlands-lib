import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionLawTransport
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Pullback and eventual descent of action laws

A prospective action map pulls back across a cartesian relation morphism and
a pullback of its object scheme. Its finite law equations descend along
cofiltered limits with affine transitions.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

section Pullback

variable {E F : EtaleEquivalenceRelation.{u}}
  {f : E.U ⟶ F.U} {g : E.R ⟶ F.R} (h : IsCartesianHom E F f g)
  {P Q : Scheme.{u}} {p : P ⟶ E.U} {q : Q ⟶ F.U}
  {k : P ⟶ Q} (hp : IsPullback k p q f)
  (b : pullback F.s q ⟶ Q) (hb : b ≫ q = pullback.fst F.s q ≫ F.t)

/-- Pull back a prospective action map using its target equation. -/
noncomputable def pullbackMap : pullback E.s p ⟶ P :=
  hp.lift (arrowMap h p q k hp.w.symm ≫ b)
    (pullback.fst E.s p ≫ E.t)
    (by rw [Category.assoc, hb, arrowMap_fst_assoc, Category.assoc, h.1])

@[reassoc (attr := simp)]
lemma pullbackMap_comparison :
    pullbackMap h hp b hb ≫ k = arrowMap h p q k hp.w.symm ≫ b :=
  hp.lift_fst _ _ _

@[reassoc]
lemma pullbackMap_over :
    pullbackMap h hp b hb ≫ p = pullback.fst E.s p ≫ E.t :=
  hp.lift_snd _ _ _

/-- The target equation and compatibility determine the pulled back map. -/
lemma pullbackMap_unique (a : pullback E.s p ⟶ P)
    (ha : a ≫ p = pullback.fst E.s p ≫ E.t)
    (hk : a ≫ k = arrowMap h p q k hp.w.symm ≫ b) :
    a = pullbackMap h hp b hb := by
  apply hp.hom_ext
  · rw [pullbackMap_comparison, hk]
  · rw [pullbackMap_over, ha]

/-- Genuine actions pull back, with the same prospective-map construction. -/
noncomputable def pullbackAction (B : Action F q) : Action E p :=
  ofEquationsAfterMap hp (pullbackMap h hp B.map B.over)
    (pullbackMap_over h hp B.map B.over)
    (by
      rw [unit_equation_naturality _ _ (pullbackMap_comparison h hp B.map B.over)]
      simp only [unitInput, B.unital, Category.comp_id])
    (by
      rw [successive_naturality _ (pullbackMap_over h hp B.map B.over) B.map B.over
          (pullbackMap_comparison h hp B.map B.over),
        composite_naturality _ _ (pullbackMap_comparison h hp B.map B.over)]
      exact congrArg (composableMap h p q k hp.w.symm ≫ ·)
        (associative_universal B))

lemma pullbackAction_isEquivariant (B : Action F q) :
    IsEquivariant h p q k hp.w.symm (pullbackAction h hp B) B :=
  pullbackMap_comparison h hp B.map B.over

end Pullback

section Eventually

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {F : EtaleEquivalenceRelation.{u}} {Q : Scheme.{u}} (q : Q ⟶ F.U)
  [LocallyOfFiniteType q]
  (D C : I ⥤ Scheme.{u})
  (v : D ⟶ (Functor.const I).obj Q)
  (z : C ⟶ (Functor.const I).obj (composable F q))
  (cD : Cone D) (hcD : IsLimit cD) (cC : Cone C) (hcC : IsLimit cC)
  [∀ i, CompactSpace (D.obj i)] [∀ i, CompactSpace (C.obj i)]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (C.map a)]

include hcD hcC in
/-- Unit and associativity equations valid at the limit hold at a common later
index. The two source diagrams may differ. -/
lemma exists_laws_at_level
    (b : pullback F.s q ⟶ Q) (hb : b ≫ q = pullback.fst F.s q ≫ F.t)
    (i : I)
    (hu : cD.π.app i ≫ v.app i ≫ unitInput q ≫ b = cD.π.app i ≫ v.app i)
    (ha : cC.π.app i ≫ z.app i ≫ successive b hb =
      cC.π.app i ≫ z.app i ≫ composite b) :
    ∃ (j : I) (_a : j ⟶ i),
      v.app j ≫ unitInput q ≫ b = v.app j ∧
      z.app j ≫ successive b hb = z.app j ≫ composite b := by
  let tD : D ⟶ (Functor.const I).obj F.U := v ≫ (Functor.const I).map q
  let tC : C ⟶ (Functor.const I).obj F.U :=
    z ≫ (Functor.const I).map (outerArrow F q ≫ F.t)
  obtain ⟨j₁, a₁, hu₁⟩ :=
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType D tD q cD hcD
      (v.app i ≫ unitInput q ≫ b) (v.app i)
      (by simp only [tD, NatTrans.comp_app, Functor.const_map_app,
        Category.assoc, unit_equation_over b hb])
      rfl hu
  obtain ⟨j₂, a₂, ha₂⟩ :=
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType C tC q cC hcC
      (z.app i ≫ successive b hb) (z.app i ≫ composite b)
      (by simp only [tC, NatTrans.comp_app, Functor.const_map_app,
        Category.assoc, successive_over b hb])
      (by simp only [tC, NatTrans.comp_app, Functor.const_map_app,
        Category.assoc, composite_over b hb])
      ha
  obtain ⟨j, d₁, d₂, hd⟩ := IsCofiltered.cospan a₁ a₂
  refine ⟨j, d₁ ≫ a₁, ?_, ?_⟩
  · have H := congrArg (D.map d₁ ≫ ·) hu₁
    simp only [← Category.assoc, v.naturality] at H
    simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.comp_id, Category.id_comp,
      Category.assoc] using H
  · have H := congrArg (C.map d₂ ≫ ·) ha₂
    simp only [← Category.assoc, z.naturality] at H
    simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.comp_id, Category.id_comp,
      Category.assoc] using H

include hcD hcC in
/-- If the object and composable diagrams are the supplied pullback levels,
eventual finite equations give an actual action at a level. -/
lemma exists_action_at_level
    (E : I → EtaleEquivalenceRelation.{u})
    (p : ∀ i, D.obj i ⟶ (E i).U)
    (f : ∀ i, (E i).U ⟶ F.U) (g : ∀ i, (E i).R ⟶ F.R)
    (h : ∀ i, IsCartesianHom (E i) F (f i) (g i))
    (hp : ∀ i, IsPullback (v.app i) (p i) q (f i))
    (e : ∀ i, composable (E i) (p i) ≅ C.obj i)
    (he : ∀ i, (e i).hom ≫ z.app i =
      composableMap (h i) (p i) q (v.app i) (hp i).w.symm)
    (b : pullback F.s q ⟶ Q) (hb : b ≫ q = pullback.fst F.s q ≫ F.t)
    (i : I)
    (hu : cD.π.app i ≫ v.app i ≫ unitInput q ≫ b = cD.π.app i ≫ v.app i)
    (ha : cC.π.app i ≫ z.app i ≫ successive b hb =
      cC.π.app i ≫ z.app i ≫ composite b) :
    ∃ (j : I) (_ : j ⟶ i) (A : Action (E j) (p j)),
      A.map ≫ v.app j = arrowMap (h j) (p j) q (v.app j) (hp j).w.symm ≫ b := by
  obtain ⟨j, a, huj, haj⟩ :=
    exists_laws_at_level q D C v z cD hcD cC hcC b hb i hu ha
  let aj := pullbackMap (h j) (hp j) b hb
  have hj : aj ≫ p j = pullback.fst (E j).s (p j) ≫ (E j).t :=
    pullbackMap_over (h j) (hp j) b hb
  have hw : aj ≫ v.app j =
      arrowMap (h j) (p j) q (v.app j) (hp j).w.symm ≫ b :=
    pullbackMap_comparison (h j) (hp j) b hb
  let A : Action (E j) (p j) := ofEquationsAfterMap (hp j) aj hj
    (by rw [unit_equation_naturality aj b hw]; exact huj)
    (by
      rw [successive_naturality aj hj b hb hw, composite_naturality aj b hw,
        ← he j]
      exact congrArg ((e j).hom ≫ ·) haj)
  exact ⟨j, a, A, hw⟩

end Eventually

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action
