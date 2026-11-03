import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionQuotientRelation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationFiniteTypeSystem
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionSystem

/-! # Diagrams of quotient relations of actions

An equivariant map `k : P' ⟶ P` from an action of `H'` to an action of `H`, over a cartesian
morphism `H' ⟶ H`, induces maps of the quotients of the action relations and of the quotients
of the pair actions. When the square formed by `k`, the two structure maps and the object map of
`H' ⟶ H` is a pullback, these maps form a cartesian morphism of the quotient relations.

A cartesian diagram of such actions over a diagram of étale equivalence relations, with chosen
quotients at every level, therefore gives a diagram of quotient relations. An action over the
point of a cone of the relation diagram, with equivariant legs and pullback squares, gives a cone
of action relations and a cone of quotient relations. If the object schemes of the relation cone
form a limit and the index category is cofiltered, then the points of the actions and the
quotients form limits as well.

Pulling back a single action of a relation `F` along a cartesian comparison from `D` to the
constant diagram on `F` gives a diagram of actions, and an action on the base change to a cone
point that is equivariant with the single action gives an action cone over it. The restriction of
`D` to the objects over an index `j` has such a comparison to the constant diagram on `D j`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

namespace Action

section Map

variable {H' H : EtaleEquivalenceRelation.{u}} {f : H'.U ⟶ H.U} {g : H'.R ⟶ H.R}
  {P' P : Scheme.{u}} {π' : P' ⟶ H'.U} {π : P ⟶ H.U} {k : P' ⟶ P}

/-- The map of pair schemes induced by a map of schemes over the object schemes. -/
noncomputable def pairObjMap (w : π' ≫ f = k ≫ π) : pullback π' π' ⟶ pullback π π :=
  pullback.map π' π' π π k k f w w

section

variable (w : π' ≫ f = k ≫ π)

@[reassoc (attr := simp)]
lemma pairObjMap_fst : pairObjMap w ≫ pullback.fst π π = pullback.fst π' π' ≫ k :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pairObjMap_snd : pairObjMap w ≫ pullback.snd π π = pullback.snd π' π' ≫ k :=
  pullback.lift_snd _ _ _

lemma pairObjMap_w :
    (pullback.fst π' π' ≫ π') ≫ f = pairObjMap w ≫ pullback.fst π π ≫ π := by
  rw [Category.assoc, pairObjMap_fst_assoc, w]

/-- If `P'` is the base change of `P` along `f`, then the pairs over `H'.U` are the base change
of the pairs over `H.U` along the first projection. -/
lemma isPullback_pairObjMap (hk : IsPullback k π' π f) :
    IsPullback (pairObjMap w) (pullback.fst π' π') (pullback.fst π π) k := by
  refine IsPullback.mk' (pairObjMap_fst w) ?_ ?_
  · intro T φ φ' h₁ h₂
    apply pullback.hom_ext h₂
    apply hk.hom_ext
    · simpa only [Category.assoc, pairObjMap_snd] using congrArg (· ≫ pullback.snd π π) h₁
    · rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% h₂]
  · intro T z b hzb
    have hc : (z ≫ pullback.snd π π) ≫ π = (b ≫ π') ≫ f := by
      simp only [Category.assoc]
      rw [← pullback.condition, reassoc_of% hzb, w]
    refine ⟨pullback.lift b (hk.lift _ _ hc) (hk.lift_snd _ _ hc).symm, ?_,
      pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pairObjMap_fst, pullback.lift_fst_assoc, hzb]
    · rw [Category.assoc, pairObjMap_snd, pullback.lift_snd_assoc, hk.lift_fst]

end

variable {h : IsCartesianHom H' H f g} {w : π' ≫ f = k ≫ π} {A' : Action H' π'}
  {A : Action H π}

/-- An equivariant map of actions is equivariant for the pair actions. -/
lemma isEquivariant_pairObjMap (hA : IsEquivariant h π' π k w A' A) :
    IsEquivariant h (pullback.fst π' π' ≫ π') (pullback.fst π π ≫ π) (pairObjMap w)
      (pairObjMap_w w) A'.pairAction A.pairAction := by
  change A'.pairMap ≫ pairObjMap w =
    arrowMap h _ _ (pairObjMap w) (pairObjMap_w w) ≫ A.pairMap
  apply pullback.hom_ext
  · rw [Category.assoc, pairObjMap_fst, pairMap_fst_assoc]
    refine (act_naturality h π' π k w A' A hA _ _ _).trans ?_
    rw [Category.assoc (arrowMap h _ _ _ _) A.pairMap, pairMap_fst, act_precomp]
    exact A.act_congr (by simp) (by simp) _ _
  · rw [Category.assoc, pairObjMap_snd, pairMap_snd_assoc]
    refine (act_naturality h π' π k w A' A hA _ _ _).trans ?_
    rw [Category.assoc (arrowMap h _ _ _ _) A.pairMap, pairMap_snd, act_precomp]
    exact A.act_congr (by simp) (by simp) _ _

lemma isCartesianHom_pairObjMap (hA : IsEquivariant h π' π k w A' A) :
    IsCartesianHom A'.pairAction.relation A.pairAction.relation (pairObjMap w)
      (arrowMap h _ _ (pairObjMap w) (pairObjMap_w w)) :=
  isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ (isEquivariant_pairObjMap hA)

variable (hA : IsEquivariant h π' π k w A' A) (Q' : A'.relation.SchemeQuotient)
  (Q : A.relation.SchemeQuotient) (Q₂' : A'.pairAction.relation.SchemeQuotient)
  (Q₂ : A.pairAction.relation.SchemeQuotient)

/-- The map of quotients of the action relations induced by an equivariant map. -/
noncomputable def quotientObjMap : Q'.M ⟶ Q.M :=
  SchemeQuotient.map (isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ hA) Q' Q

@[reassoc (attr := simp)]
lemma q_quotientObjMap : Q'.q ≫ quotientObjMap hA Q' Q = k ≫ Q.q :=
  SchemeQuotient.q_map _ _ _

lemma isPullback_quotientObjMap : IsPullback k Q'.q Q.q (quotientObjMap hA Q' Q) :=
  SchemeQuotient.isPullback_map (isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ hA) Q' Q

lemma isAffineHom_quotientObjMap [IsAffineHom k] [IsAffineHom Q.q] :
    IsAffineHom (quotientObjMap hA Q' Q) :=
  SchemeQuotient.isAffineHom_map (isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ hA) Q' Q

/-- The map of quotients of the pair action relations induced by an equivariant map. -/
noncomputable def quotientRelMap : Q₂'.M ⟶ Q₂.M :=
  SchemeQuotient.map (isCartesianHom_pairObjMap hA) Q₂' Q₂

@[reassoc (attr := simp)]
lemma q_quotientRelMap : Q₂'.q ≫ quotientRelMap hA Q₂' Q₂ = pairObjMap w ≫ Q₂.q :=
  SchemeQuotient.q_map _ _ _

@[reassoc]
lemma quotientRelMap_quotientS :
    quotientRelMap hA Q₂' Q₂ ≫ A.quotientS Q Q₂ = A'.quotientS Q' Q₂' ≫ quotientObjMap hA Q' Q :=
  Q₂'.hom_ext (by simp)

@[reassoc]
lemma quotientRelMap_quotientT :
    quotientRelMap hA Q₂' Q₂ ≫ A.quotientT Q Q₂ = A'.quotientT Q' Q₂' ≫ quotientObjMap hA Q' Q :=
  Q₂'.hom_ext (by simp)

/-- If `P'` is the base change of `P`, the square formed by the induced maps of quotients and
the two source maps of the quotient relations is a pullback. -/
theorem isPullback_quotientRelMap (hk : IsPullback k π' π f) :
    IsPullback (quotientRelMap hA Q₂' Q₂) (A'.quotientS Q' Q₂') (A.quotientS Q Q₂)
      (quotientObjMap hA Q' Q) := by
  have top := isPullback_pairObjMap w hk
  have front := A.isPullback_quotientS Q Q₂
  have back := A'.isPullback_quotientS Q' Q₂'
  refine isPullback_of_exists_local (quotientRelMap_quotientS hA Q' Q Q₂' Q₂) ?_ ?_
  · intro T φ φ' hR hS
    let e : pullback φ Q₂'.q ⟶ T := pullback.fst φ Q₂'.q
    let x : pullback φ Q₂'.q ⟶ pullback π' π' := pullback.snd φ Q₂'.q
    have hx : x ≫ Q₂'.q = e ≫ φ := pullback.condition.symm
    have he : Epi e := by
      dsimp only [e]
      infer_instance
    clear_value e x
    have hy : (x ≫ pullback.fst π' π') ≫ Q'.q = (e ≫ φ') ≫ A'.quotientS Q' Q₂' := by
      simp only [Category.assoc]
      rw [← A'.q_quotientS Q' Q₂', reassoc_of% hx, hS]
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y, y ≫ pullback.fst π' π' = x ≫ pullback.fst π' π' ∧
        y ≫ Q₂'.q = e ≫ φ' :=
      ⟨back.lift _ _ hy, back.lift_fst _ _ _, back.lift_snd _ _ _⟩
    have hxy : x = y := by
      apply top.hom_ext _ hy₁.symm
      apply front.hom_ext
      · simp only [Category.assoc, pairObjMap_fst]
        rw [reassoc_of% hy₁]
      · simp only [Category.assoc]
        rw [← q_quotientRelMap hA Q₂' Q₂, reassoc_of% hx, reassoc_of% hy₂, hR]
    have : e ≫ φ = e ≫ φ' := by rw [← hx, ← hy₂, hxy]
    exact (cancel_epi e).1 this
  · intro T a b hab
    let e : pullback b Q'.q ⟶ T := pullback.fst b Q'.q
    let b' : pullback b Q'.q ⟶ P' := pullback.snd b Q'.q
    have hb' : e ≫ b = b' ≫ Q'.q := pullback.condition
    have he : EffectiveEpi e := by
      dsimp only [e]
      infer_instance
    clear_value e b'
    have hz : (b' ≫ k) ≫ Q.q = (e ≫ a) ≫ A.quotientS Q Q₂ := by
      simp only [Category.assoc]
      rw [hab, ← q_quotientObjMap hA Q' Q, reassoc_of% hb']
    obtain ⟨z, hz₁, hz₂⟩ : ∃ z, z ≫ pullback.fst π π = b' ≫ k ∧ z ≫ Q₂.q = e ≫ a :=
      ⟨front.lift _ _ hz, front.lift_fst _ _ _, front.lift_snd _ _ _⟩
    obtain ⟨z', hz'₁, hz'₂⟩ : ∃ z', z' ≫ pairObjMap w = z ∧ z' ≫ pullback.fst π' π' = b' :=
      ⟨top.lift _ _ hz₁, top.lift_fst _ _ _, top.lift_snd _ _ _⟩
    refine ⟨pullback b Q'.q, e, z' ≫ Q₂'.q, he, ?_, ?_⟩
    · rw [Category.assoc, q_quotientRelMap, reassoc_of% hz'₁, hz₂]
    · rw [Category.assoc, A'.q_quotientS, reassoc_of% hz'₂, hb']

variable [Etale π'] [Etale π]

/-- The induced maps of quotients form a cartesian morphism of quotient relations when `P'` is
the base change of `P`. -/
theorem isCartesianHom_quotientRelation (hk : IsPullback k π' π f) :
    IsCartesianHom (A'.quotientRelation Q' Q₂') (A.quotientRelation Q Q₂)
      (quotientObjMap hA Q' Q) (quotientRelMap hA Q₂' Q₂) :=
  ⟨quotientRelMap_quotientT hA Q' Q Q₂' Q₂, isPullback_quotientRelMap hA Q' Q Q₂' Q₂ hk⟩

/-- The cartesian morphism of quotient relations induced by an equivariant map whose square of
structure maps is a pullback. -/
noncomputable def quotientRelationHom (hk : IsPullback k π' π f) :
    A'.quotientRelation Q' Q₂' ⟶ A.quotientRelation Q Q₂ :=
  ⟨quotientObjMap hA Q' Q, quotientRelMap hA Q₂' Q₂,
    isCartesianHom_quotientRelation hA Q' Q Q₂' Q₂ hk⟩

@[simp]
lemma quotientRelationHom_objMap (hk : IsPullback k π' π f) :
    (quotientRelationHom hA Q' Q Q₂' Q₂ hk).objMap = quotientObjMap hA Q' Q := rfl

@[simp]
lemma quotientRelationHom_relMap (hk : IsPullback k π' π f) :
    (quotientRelationHom hA Q' Q Q₂' Q₂ hk).relMap = quotientRelMap hA Q₂' Q₂ := rfl

end Map

section PullbackAction

variable {E' E F : EtaleEquivalenceRelation.{u}} {f₁ : E'.U ⟶ E.U} {g₁ : E'.R ⟶ E.R}
  {f₂ : E.U ⟶ F.U} {g₂ : E.R ⟶ F.R} {f : E'.U ⟶ F.U} {g : E'.R ⟶ F.R}
  {P' P Q : Scheme.{u}} {p' : P' ⟶ E'.U} {p : P ⟶ E.U} {q : Q ⟶ F.U}

/-- Let `(f₁, g₁) : E' ⟶ E`, `(f₂, g₂) : E ⟶ F` and `(f, g) : E' ⟶ F` be cartesian morphisms
with `g₁ ≫ g₂ = g`, and let `P` be the base change of `Q` along `f₂`. An action on `P'` that is
equivariant over `(f, g)` with an action `B` on `Q`, via a map `P' ⟶ Q` factoring through
`l : P' ⟶ P`, is equivariant via `l` with the pulled back action of `B` on `P`. -/
lemma isEquivariant_pullbackAction_of_comp (h₁ : IsCartesianHom E' E f₁ g₁)
    (h₂ : IsCartesianHom E F f₂ g₂) (h : IsCartesianHom E' F f g)
    (hg : g₁ ≫ g₂ = g) {k : P ⟶ Q} (hp : IsPullback k p q f₂) {l : P' ⟶ P}
    (w : p' ≫ f₁ = l ≫ p) {k' : P' ⟶ Q} (hk : l ≫ k = k') (w' : p' ≫ f = k' ≫ q)
    (A : Action E' p') (B : Action F q) (hA : IsEquivariant h p' q k' w' A B) :
    IsEquivariant h₁ p' p l w A (pullbackAction h₂ hp B) := by
  change A.map ≫ l = arrowMap h₁ p' p l w ≫ pullbackMap h₂ hp B.map B.over
  apply hp.hom_ext
  · have hA' : A.map ≫ k' = arrowMap h p' q k' w' ≫ B.map := hA
    have harrow : arrowMap h₁ p' p l w ≫ arrowMap h₂ p q k hp.w.symm =
        arrowMap h p' q k' w' := by
      apply pullback.hom_ext
      · simp only [Category.assoc, arrowMap_fst, arrowMap_fst_assoc, hg]
      · simp only [Category.assoc, arrowMap_snd, arrowMap_snd_assoc, hk]
    rw [Category.assoc, hk, hA', ← harrow, Category.assoc, Category.assoc,
      pullbackMap_comparison]
  · calc (A.map ≫ l) ≫ p = (A.map ≫ p') ≫ f₁ := by
          rw [Category.assoc, Category.assoc, w]
      _ = (pullback.fst E'.s p' ≫ E'.t) ≫ f₁ := by rw [A.over]
      _ = (arrowMap h₁ p' p l w ≫ pullbackMap h₂ hp B.map B.over) ≫ p := by
          simp only [Category.assoc, pullbackMap_over, arrowMap_fst_assoc, h₁.1]

end PullbackAction

namespace CartesianSystem

variable {I : Type u} [Category.{u} I] {D : I ⥤ EtaleEquivalenceRelation.{u}}
  {F : EtaleEquivalenceRelation.{u}} (t : D ⟶ (Functor.const I).obj F)
  {Q : Scheme.{u}} {q : Q ⟶ F.U}

lemma comparison_naturality_objMap {i j : I} (a : i ⟶ j) :
    (D.map a).objMap ≫ (t.app j).objMap = (t.app i).objMap :=
  congrArg CartesianMorphism.objMap ((t.naturality a).trans (Category.comp_id _))

lemma comparison_naturality_relMap {i j : I} (a : i ⟶ j) :
    (D.map a).relMap ≫ (t.app j).relMap = (t.app i).relMap :=
  congrArg CartesianMorphism.relMap ((t.naturality a).trans (Category.comp_id _))

lemma pointComparison_naturality {i j : I} (a : i ⟶ j) :
    (objectDiagram D t (q := q)).map a ≫ (pointComparison D t (q := q)).app j =
      (pointComparison D t (q := q)).app i :=
  ((pointComparison D t (q := q)).naturality a).trans (Category.comp_id _)

lemma objectMap_naturality {i j : I} (a : i ⟶ j) :
    objectMap D t (q := q) i ≫ (D.map a).objMap =
      (objectDiagram D t (q := q)).map a ≫ objectMap D t (q := q) j :=
  ((TargetLimit.projection (D ⋙ objectFunctor) (objectComparison D t) q).naturality a).symm

/-- The square formed by a transition map of the pulled back objects, the structure maps and
the corresponding object map of `D` is a pullback. -/
lemma isPullback_objectDiagram_map {i j : I} (a : i ⟶ j) :
    IsPullback ((objectDiagram D t (q := q)).map a) (objectMap D t (q := q) i)
      (objectMap D t (q := q) j) (D.map a).objMap := by
  have H := object_isPullback D t (q := q) i
  rw [← pointComparison_naturality t a, ← comparison_naturality_objMap t a] at H
  exact H.of_right (objectMap_naturality t a).symm (object_isPullback D t (q := q) j)

end CartesianSystem

end Action

/-- A diagram of actions over a diagram `D` of étale equivalence relations: a diagram of schemes
`points` with étale structure maps `proj i` to the object schemes of `D`, an action of `D i` on
each `proj i`, equivariant transition maps, and pullback squares of structure maps. -/
structure ActionDiagram {I : Type u} [Category.{u} I] (D : I ⥤ EtaleEquivalenceRelation.{u}) where
  points : I ⥤ Scheme.{u}
  proj : ∀ i, points.obj i ⟶ (D.obj i).U
  proj_w : ∀ {i j : I} (a : i ⟶ j), proj i ≫ (D.map a).objMap = points.map a ≫ proj j
  action : ∀ i, Action (D.obj i) (proj i)
  etale : ∀ i, Etale (proj i)
  isEquivariant : ∀ {i j : I} (a : i ⟶ j),
    Action.IsEquivariant (D.map a).isCartesian (proj i) (proj j) (points.map a) (proj_w a)
      (action i) (action j)
  isPullback : ∀ {i j : I} (a : i ⟶ j),
    IsPullback (points.map a) (proj i) (proj j) (D.map a).objMap

namespace ActionDiagram

attribute [instance] ActionDiagram.etale

variable {I : Type u} [Category.{u} I] {D : I ⥤ EtaleEquivalenceRelation.{u}}
  (A : ActionDiagram D)

/-- An action over the point of a cone `c` of the relation diagram, with equivariant legs to the
actions of the diagram and pullback squares of structure maps. -/
structure ActionCone (c : Cone D) where
  P : Scheme.{u}
  proj : P ⟶ c.pt.U
  action : Action c.pt proj
  etale : Etale proj
  leg : ∀ i, P ⟶ A.points.obj i
  leg_w : ∀ i, proj ≫ (c.π.app i).objMap = leg i ≫ A.proj i
  leg_comp : ∀ {i j : I} (a : i ⟶ j), leg i ≫ A.points.map a = leg j
  isEquivariant : ∀ i,
    Action.IsEquivariant (c.π.app i).isCartesian proj (A.proj i) (leg i) (leg_w i) action
      (A.action i)
  isPullback : ∀ i, IsPullback (leg i) proj (A.proj i) (c.π.app i).objMap

attribute [instance] ActionCone.etale

/-- The diagram of action relations. -/
@[simps]
noncomputable def relationDiagram : I ⥤ EtaleEquivalenceRelation.{u} where
  obj i := (A.action i).relation
  map a := ⟨A.points.map a, Action.arrowMap (D.map a).isCartesian _ _ _ (A.proj_w a),
    Action.isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ (A.isEquivariant a)⟩
  map_id i := by
    apply CartesianMorphism.ext
    · exact A.points.map_id i
    · apply pullback.hom_ext <;> simp
  map_comp a b := by
    apply CartesianMorphism.ext
    · exact A.points.map_comp a b
    · apply pullback.hom_ext <;> simp

variable {c : Cone D} (T : A.ActionCone c)

/-- The cone of action relations with point the action relation of the cone point. -/
@[simps]
noncomputable def relationCone : Cone A.relationDiagram where
  pt := T.action.relation
  π :=
    { app i := ⟨T.leg i, Action.arrowMap (c.π.app i).isCartesian _ _ _ (T.leg_w i),
        Action.isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ (T.isEquivariant i)⟩
      naturality i j a := by
        have hw : (c.π.app i).relMap ≫ (D.map a).relMap = (c.π.app j).relMap :=
          congrArg CartesianMorphism.relMap (c.w a)
        apply CartesianMorphism.ext
        · simp [T.leg_comp a]
        · apply pullback.hom_ext
          · simp [hw]
          · simp [T.leg_comp a] }

/-- If the object schemes of the relation cone form a limit, then so do the points of the
actions: the point of each action is the base change of a level along the cone leg. -/
noncomputable def isLimitRelationConeObject [IsCofiltered I]
    (hc : IsLimit (objectFunctor.mapCone c)) :
    IsLimit (objectFunctor.mapCone (A.relationCone T)) := by
  refine IsLimit.ofExistsUnique fun S => ?_
  let j₀ : I := (IsCofiltered.nonempty (C := I)).some
  have hS : ∀ {i j : I} (a : i ⟶ j), S.π.app i ≫ A.points.map a = S.π.app j := fun a =>
    (S.π.naturality a).symm.trans (Category.id_comp _)
  let S' : Cone (D ⋙ objectFunctor) :=
    { pt := S.pt
      π :=
        { app i := S.π.app i ≫ A.proj i
          naturality i j a := by
            change 𝟙 S.pt ≫ S.π.app j ≫ A.proj j = (S.π.app i ≫ A.proj i) ≫ (D.map a).objMap
            rw [Category.id_comp, Category.assoc, A.proj_w, reassoc_of% (hS a)] } }
  have hu : ∀ i, hc.lift S' ≫ (c.π.app i).objMap = S.π.app i ≫ A.proj i := hc.fac S'
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, m ≫ T.leg j₀ = S.π.app j₀ ∧ m ≫ T.proj = hc.lift S' :=
    ⟨(T.isPullback j₀).lift _ _ (hu j₀).symm, (T.isPullback j₀).lift_fst _ _ _,
      (T.isPullback j₀).lift_snd _ _ _⟩
  have hm : ∀ i, m ≫ T.leg i = S.π.app i := by
    intro i
    let k := IsCofiltered.min i j₀
    have hk : m ≫ T.leg k = S.π.app k := by
      apply (A.isPullback (IsCofiltered.minToRight i j₀)).hom_ext
      · rw [Category.assoc, T.leg_comp, hm₁, hS]
      · rw [Category.assoc, ← T.leg_w, reassoc_of% hm₂, hu]
    rw [← T.leg_comp (IsCofiltered.minToLeft i j₀), reassoc_of% hk, hS]
  refine ⟨m, hm, fun m' hm' => ?_⟩
  have hm'' : ∀ i, m' ≫ T.leg i = S.π.app i := hm'
  apply (T.isPullback j₀).hom_ext
  · rw [hm'' j₀, hm₁]
  · rw [hm₂]
    apply hc.hom_ext
    intro i
    change (m' ≫ T.proj) ≫ (c.π.app i).objMap = hc.lift S' ≫ (c.π.app i).objMap
    rw [hu, Category.assoc, T.leg_w, reassoc_of% (hm'' i)]

variable (Q : ∀ i, (A.action i).relation.SchemeQuotient)
  (Q₂ : ∀ i, (A.action i).pairAction.relation.SchemeQuotient)

/-- The diagram of quotient relations of a diagram of actions with chosen quotients. -/
@[simps]
noncomputable def quotientRelationDiagram : I ⥤ EtaleEquivalenceRelation.{u} where
  obj i := (A.action i).quotientRelation (Q i) (Q₂ i)
  map a := Action.quotientRelationHom (A.isEquivariant a) (Q _) (Q _) (Q₂ _) (Q₂ _)
    (A.isPullback a)
  map_id i := by
    have h₂ : Action.pairObjMap (A.proj_w (𝟙 i)) = 𝟙 _ := by
      apply pullback.hom_ext <;> simp
    apply CartesianMorphism.ext
    · apply (Q i).hom_ext
      simp only [Action.quotientRelationHom_objMap, Action.q_quotientObjMap, id_objMap]
      exact (congrArg (· ≫ (Q i).q) (A.points.map_id i)).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm)
    · apply (Q₂ i).hom_ext
      simp only [Action.quotientRelationHom_relMap,
        Action.q_quotientRelMap, id_relMap, h₂]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  map_comp {i j k} a b := by
    have h₂ : Action.pairObjMap (A.proj_w (a ≫ b)) =
        Action.pairObjMap (A.proj_w a) ≫ Action.pairObjMap (A.proj_w b) := by
      apply pullback.hom_ext <;> simp
    apply CartesianMorphism.ext
    · apply (Q i).hom_ext
      simp only [Action.quotientRelationHom_objMap,
        Action.q_quotientObjMap, Action.q_quotientObjMap_assoc, comp_objMap, Functor.map_comp,
        Category.assoc]
    · apply (Q₂ i).hom_ext
      simp only [Action.quotientRelationHom_relMap,
        Action.q_quotientRelMap, Action.q_quotientRelMap_assoc, comp_relMap, h₂, Category.assoc]

lemma isAffineHom_quotientRelationDiagram_map [∀ i, IsAffineHom (Q i).q]
    (hD : ∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).objMap) {i j : I} (a : i ⟶ j) :
    IsAffineHom ((A.quotientRelationDiagram Q Q₂).map a).objMap :=
  have := hD a
  have : IsAffineHom (A.points.map a) := MorphismProperty.of_isPullback (A.isPullback a).flip this
  Action.isAffineHom_quotientObjMap (A.isEquivariant a) (Q i) (Q j)

variable (Qc : T.action.relation.SchemeQuotient) (Q₂c : T.action.pairAction.relation.SchemeQuotient)

/-- The cone of quotient relations with point the quotient relation of the cone point. -/
@[simps]
noncomputable def quotientRelationCone : Cone (A.quotientRelationDiagram Q Q₂) where
  pt := T.action.quotientRelation Qc Q₂c
  π :=
    { app i := Action.quotientRelationHom (T.isEquivariant i) Qc (Q i) Q₂c (Q₂ i)
        (T.isPullback i)
      naturality i j a := by
        have h₂ : Action.pairObjMap (T.leg_w i) ≫ Action.pairObjMap (A.proj_w a) =
            Action.pairObjMap (T.leg_w j) := by
          apply pullback.hom_ext <;> simp [T.leg_comp a]
        apply CartesianMorphism.ext
        · apply Qc.hom_ext
          simp [reassoc_of% (T.leg_comp a)]
        · apply Q₂c.hom_ext
          simp [reassoc_of% h₂] }

/-- The diagram of quotients of the action relations is the diagram of object schemes of the
quotient relations. -/
noncomputable def quotientFunctorIso :
    SchemeQuotient.quotientFunctor A.relationDiagram Q ≅
      A.quotientRelationDiagram Q Q₂ ⋙ objectFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- If the points of the actions form a limit, then the object scheme of the quotient relation
of the cone point is the limit of the object schemes of the quotient relations. -/
noncomputable def isLimitQuotientRelationConeOfIsLimit [IsCofiltered I]
    (hP : IsLimit (objectFunctor.mapCone (A.relationCone T))) :
    IsLimit (objectFunctor.mapCone (A.quotientRelationCone T Q Q₂ Qc Q₂c)) :=
  IsLimit.equivOfNatIsoOfIso (A.quotientFunctorIso Q Q₂)
    (SchemeQuotient.quotientCone Q (A.relationCone T) Qc)
    (objectFunctor.mapCone (A.quotientRelationCone T Q Q₂ Qc Q₂c))
    (Cone.ext (Iso.refl _) fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)
    (SchemeQuotient.isLimitQuotientCone Q (A.relationCone T) Qc hP)

/-- If the object schemes of the relation cone form a limit, then the object scheme of the
quotient relation of the cone point is the limit of the object schemes of the quotient
relations. -/
noncomputable def isLimitQuotientRelationCone [IsCofiltered I]
    (hc : IsLimit (objectFunctor.mapCone c)) :
    IsLimit (objectFunctor.mapCone (A.quotientRelationCone T Q Q₂ Qc Q₂c)) :=
  A.isLimitQuotientRelationConeOfIsLimit T Q Q₂ Qc Q₂c (A.isLimitRelationConeObject T hc)

section FiniteTypeSystem

variable [IsCofiltered I] (hc : IsLimit (objectFunctor.mapCone c))
  {E : EtaleEquivalenceRelation.{u}} (φ : E ⟶ T.action.quotientRelation Qc Q₂c) [IsIso φ.objMap]

/-- The cone of quotient relations extended along a cartesian morphism whose object map is an
isomorphism is still a limit on object schemes. -/
noncomputable def isLimitQuotientRelationConeExtend :
    IsLimit (objectFunctor.mapCone ((A.quotientRelationCone T Q Q₂ Qc Q₂c).extend φ)) :=
  IsLimit.ofIsoLimit (A.isLimitQuotientRelationCone T Q Q₂ Qc Q₂c hc)
    (Cone.ext (asIso φ.objMap).symm fun i => by
      simp only [Functor.mapCone_π_app, objectFunctor_map, Cone.extend_π, NatTrans.comp_app,
        Functor.const_map_app, comp_objMap, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc])

/-- A finite type cartesian system for `E`, built from a diagram of actions with chosen quotients,
an action over the point of a cone with limit object schemes, and a cartesian morphism from `E` to
the quotient relation of the cone point whose object map is an isomorphism. -/
noncomputable def finiteTypeCartesianSystem
    [∀ i, CompactSpace (A.points.obj i)] [∀ i, LocallyOfFiniteType (terminal.from (A.points.obj i))]
    [∀ i, IsAffineHom (A.proj i)]
    [∀ i, QuasiSeparatedSpace (pullback (A.proj i) (A.proj i) : Scheme.{u})]
    [∀ i, IsAffineHom (Q i).q]
    (hD : ∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).objMap) :
    FiniteTypeCartesianSystem E where
  Index := I
  diagram := A.quotientRelationDiagram Q Q₂
  comparison := ((A.quotientRelationCone T Q Q₂ Qc Q₂c).extend φ).π
  isLimitObject := A.isLimitQuotientRelationConeExtend T Q Q₂ Qc Q₂c hc φ
  object_compact i := (A.action i).compactSpace_quotientRelation_U (Q i) (Q₂ i)
  object_finiteType i := (A.action i).locallyOfFiniteType_quotientRelation_U (Q i) (Q₂ i)
  relation_compact i := (A.action i).compactSpace_quotientRelation_R (Q i) (Q₂ i)
  relation_quasiSeparated i := (A.action i).quasiSeparatedSpace_quotientRelation_R (Q i) (Q₂ i)
  source_isSeparated i := (A.action i).isSeparated_quotientRelation_s (Q i) (Q₂ i)
  objectMap_isAffine a := A.isAffineHom_quotientRelationDiagram_map Q Q₂ hD a

@[simp]
lemma finiteTypeCartesianSystem_diagram
    [∀ i, CompactSpace (A.points.obj i)] [∀ i, LocallyOfFiniteType (terminal.from (A.points.obj i))]
    [∀ i, IsAffineHom (A.proj i)]
    [∀ i, QuasiSeparatedSpace (pullback (A.proj i) (A.proj i) : Scheme.{u})]
    [∀ i, IsAffineHom (Q i).q]
    (hD : ∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).objMap) :
    (A.finiteTypeCartesianSystem T Q Q₂ Qc Q₂c hc φ hD).diagram = A.quotientRelationDiagram Q Q₂ :=
  rfl

end FiniteTypeSystem

section Comparison

open Action.CartesianSystem

variable {F : EtaleEquivalenceRelation.{u}} (t : D ⟶ (Functor.const I).obj F)
  {Q : Scheme.{u}} {q : Q ⟶ F.U} [Etale q] (B : Action F q)

/-- The diagram of actions obtained by pulling back a single action `B` of `F` on `q : Q ⟶ F.U`
along a cartesian comparison `t` from `D` to the constant diagram on `F`: at level `i` the points
are `(D i).U ×_{F.U} Q` with the pulled back action. -/
@[simps]
noncomputable def ofComparison : ActionDiagram D where
  points := objectDiagram D t (q := q)
  proj := objectMap D t (q := q)
  proj_w a := objectMap_naturality t a
  action i := Action.pullbackAction (t.app i).isCartesian (object_isPullback D t (q := q) i) B
  etale i := by
    change Etale (pullback.fst _ _)
    infer_instance
  isEquivariant {i j} a :=
    Action.isEquivariant_pullbackAction_of_comp (D.map a).isCartesian (t.app j).isCartesian
      (t.app i).isCartesian (comparison_naturality_relMap t a) (object_isPullback D t (q := q) j)
      (objectMap_naturality t a) (pointComparison_naturality t a)
      (object_isPullback D t (q := q) i).w.symm _ B
      (Action.pullbackAction_isEquivariant _ _ B)
  isPullback a := isPullback_objectDiagram_map t a

variable {c : Cone D} (m : c.pt ⟶ F) (hm : ∀ i, c.π.app i ≫ t.app i = m) {P : Scheme.{u}}
  {p : P ⟶ c.pt.U} {k : P ⟶ Q} (hp : IsPullback k p q m.objMap) [Etale p]
  (A : Action c.pt p)

/-- An action on the base change of `Q` to the cone point, equivariant with `B`, gives an action
cone over the diagram of pulled back actions. -/
@[simps]
noncomputable def ActionCone.ofComparison
    (hA : Action.IsEquivariant m.isCartesian p q k hp.w.symm A B) :
    (ActionDiagram.ofComparison t B).ActionCone c where
  P := P
  proj := p
  action := A
  etale := inferInstance
  leg i := (objectCone D t c m hm hp).π.app i
  leg_w i := (objectCone_π_object D t c m hm hp i).symm
  leg_comp a := ((objectCone D t c m hm hp).w a)
  isEquivariant i :=
    Action.isEquivariant_pullbackAction_of_comp (c.π.app i).isCartesian (t.app i).isCartesian
      m.isCartesian (congrArg CartesianMorphism.relMap (hm i)) (object_isPullback D t (q := q) i)
      (objectCone_π_object D t c m hm hp i).symm (objectCone_π_point D t c m hm hp i)
      hp.w.symm A B hA
  isPullback i := objectCone_isPullback D t c m hm hp i

end Comparison

section Over

/-- The comparison from the restriction of `D` to the category of objects over `j` to the
constant diagram on `D j`, given by the transition maps to `j`. -/
@[simps]
def overComparison (D : I ⥤ EtaleEquivalenceRelation.{u}) (j : I) :
    Over.forget j ⋙ D ⟶ (Functor.const (Over j)).obj (D.obj j) :=
  CartesianDiagram.comparison D j

lemma whisker_overComparison (D : I ⥤ EtaleEquivalenceRelation.{u}) (c : Cone D) (j : I)
    (X : Over j) :
    (c.whisker (Over.forget j)).π.app X ≫ (overComparison D j).app X = c.π.app j :=
  c.w X.hom

end Over

end ActionDiagram

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
