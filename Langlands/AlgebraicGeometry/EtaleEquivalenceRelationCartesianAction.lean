import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAction

/-! # The action associated to a cartesian relation morphism

The source pullback square uniquely lifts an arrow with a prescribed source.
Its target defines an action of the lower relation on the upper object scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.IsCartesianHom

variable {E F : EtaleEquivalenceRelation.{u}} {f : E.U ⟶ F.U} {g : E.R ⟶ F.R}
  (h : IsCartesianHom E F f g)

include h in
/-- A cartesian relation morphism preserves units. -/
lemma unit_naturality : E.unit ≫ g = f ≫ F.unit := by
  apply F.hom_ext <;> simp [h.1, h.2.w]

/-- A cartesian relation morphism preserves composition. -/
lemma compose_naturality {T : Scheme.{u}} (r q : T ⟶ E.R)
    (hrq : r ≫ E.s = q ≫ E.t) :
    E.compose r q hrq ≫ g =
      F.compose (r ≫ g) (q ≫ g)
        (by rw [Category.assoc, h.2.w, ← Category.assoc, hrq, Category.assoc, ← h.1,
          ← Category.assoc]) := by
  apply F.hom_ext <;> simp [h.1, h.2.w]

/-- Lift a lower arrow with its prescribed upper source. -/
noncomputable def liftArrow {T : Scheme.{u}} (r : T ⟶ F.R) (v : T ⟶ E.U)
    (hv : r ≫ F.s = v ≫ f) : T ⟶ E.R :=
  h.2.lift r v hv

@[reassoc (attr := simp)]
lemma liftArrow_g {T : Scheme.{u}} (r : T ⟶ F.R) (v : T ⟶ E.U)
    (hv : r ≫ F.s = v ≫ f) : h.liftArrow r v hv ≫ g = r :=
  h.2.lift_fst r v hv

@[reassoc (attr := simp)]
lemma liftArrow_s {T : Scheme.{u}} (r : T ⟶ F.R) (v : T ⟶ E.U)
    (hv : r ≫ F.s = v ≫ f) : h.liftArrow r v hv ≫ E.s = v :=
  h.2.lift_snd r v hv

@[reassoc (attr := simp)]
lemma liftArrow_t_over {T : Scheme.{u}} (r : T ⟶ F.R) (v : T ⟶ E.U)
    (hv : r ≫ F.s = v ≫ f) : h.liftArrow r v hv ≫ E.t ≫ f = r ≫ F.t := by
  rw [← h.1, ← Category.assoc, h.liftArrow_g]

lemma liftArrow_unit {T : Scheme.{u}} (v : T ⟶ E.U) :
    h.liftArrow (v ≫ f ≫ F.unit) v (by simp) = v ≫ E.unit := by
  apply h.2.hom_ext
  · simp [h.unit_naturality]
  · simp

/-- The action map is the target of the unique upper arrow. -/
noncomputable def actionMap : pullback F.s f ⟶ E.U :=
  h.2.isoPullback.inv ≫ E.t

@[reassoc]
lemma actionMap_over : h.actionMap ≫ f = pullback.fst F.s f ≫ F.t := by
  rw [actionMap, Category.assoc, ← h.1, ← Category.assoc, h.2.isoPullback_inv_fst]

lemma lift_actionMap {T : Scheme.{u}} (r : T ⟶ F.R) (v : T ⟶ E.U)
    (hv : r ≫ F.s = v ≫ f) :
    pullback.lift r v hv ≫ h.actionMap = h.liftArrow r v hv ≫ E.t := by
  dsimp only [actionMap]
  rw [← Category.assoc]
  apply congrArg (· ≫ E.t)
  apply h.2.hom_ext
  · simp [liftArrow, pullback.lift_fst]
  · simp [liftArrow, pullback.lift_snd]

lemma liftArrow_comp {T : Scheme.{u}} (r q : T ⟶ F.R) (v : T ⟶ E.U)
    (hrq : r ≫ F.s = q ≫ F.t) (hqv : q ≫ F.s = v ≫ f) :
    h.liftArrow (F.compose r q hrq) v (by simpa using hqv) =
      E.compose
        (h.liftArrow r (h.liftArrow q v hqv ≫ E.t)
          (by rw [Category.assoc, h.liftArrow_t_over]; exact hrq))
        (h.liftArrow q v hqv) (by simp) := by
  apply h.2.hom_ext
  · simp only [h.liftArrow_g, h.compose_naturality]
  · simp

/-- A cartesian relation morphism equips its object scheme with a canonical action. -/
noncomputable def action : Action F f where
  map := h.actionMap
  over := h.actionMap_over
  unital := by
    rw [h.lift_actionMap]
    simpa using congrArg (· ≫ E.t) (h.liftArrow_unit (𝟙 E.U))
  associative := by
    intro T r q v hrq hqv
    simp only [h.lift_actionMap]
    rw [h.liftArrow_comp, compose_t]

lemma action_act {T : Scheme.{u}} (r : T ⟶ F.R) (v : T ⟶ E.U)
    (hv : r ≫ F.s = v ≫ f) :
    h.action.act r v hv = h.liftArrow r v hv ≫ E.t :=
  h.lift_actionMap r v hv

/-- The source pullback identifies the upper arrows with the canonical action arrows. -/
noncomputable def actionRelationIso : E.R ≅ h.action.relation.R :=
  h.2.isoPullback

@[reassoc (attr := simp)]
lemma actionRelationIso_t :
    h.actionRelationIso.hom ≫ h.action.relation.t = E.t := by
  change h.2.isoPullback.hom ≫ h.2.isoPullback.inv ≫ E.t = E.t
  simp

@[reassoc (attr := simp)]
lemma actionRelationIso_s :
    h.actionRelationIso.hom ≫ h.action.relation.s = E.s :=
  h.2.isoPullback_hom_snd

/-- The canonical action relation is cartesian isomorphic to the upper relation. -/
lemma isCartesianHom_action :
    IsCartesianHom E h.action.relation (𝟙 E.U) h.actionRelationIso.hom := by
  constructor
  · change h.2.isoPullback.hom ≫ (h.2.isoPullback.inv ≫ E.t) = E.t ≫ 𝟙 E.U
    simp
  · change IsPullback h.actionRelationIso.hom E.s (pullback.snd F.s f) (𝟙 E.U)
    apply IsPullback.of_horiz_isIso
    refine ⟨?_⟩
    change h.2.isoPullback.hom ≫ pullback.snd F.s f = E.s ≫ 𝟙 E.U
    simp

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.IsCartesianHom
