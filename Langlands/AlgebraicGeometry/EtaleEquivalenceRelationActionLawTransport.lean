import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionLaws
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionMorphism
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianAction

/-! # Transport of the finite action equations

The unit and universal associativity equations are natural under compatible
maps of prospective actions. A pullback square on the action objects then
allows these equations to be checked after composition to a lower level.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

variable {E F : EtaleEquivalenceRelation.{u}}
  {f : E.U ⟶ F.U} {g : E.R ⟶ F.R} (h : IsCartesianHom E F f g)
  {P Q : Scheme.{u}} (p : P ⟶ E.U) (q : Q ⟶ F.U)
  (k : P ⟶ Q) (w : p ≫ f = k ≫ q)

/-- Insert the identity arrow at an action point. -/
noncomputable def unitInput : P ⟶ pullback E.s p :=
  pullback.lift (p ≫ E.unit) (𝟙 P) (by simp)

@[reassoc (attr := simp)]
lemma unitInput_fst : unitInput p ≫ pullback.fst E.s p = p ≫ E.unit :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma unitInput_snd : unitInput p ≫ pullback.snd E.s p = 𝟙 P :=
  pullback.lift_snd _ _ _

/-- The universal action input respects units. -/
lemma unitInput_arrowMap :
    unitInput p ≫ arrowMap h p q k w = k ≫ unitInput q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, arrowMap_fst, unitInput_fst_assoc, unitInput_fst]
    rw [h.unit_naturality, ← Category.assoc, w, Category.assoc]
  · simp

/-- Send a universal composable pair and its source point to the lower level. -/
noncomputable def composableMap : composable E p ⟶ composable F q :=
  composableLift F q (outerArrow E p ≫ g) (innerArrow E p ≫ g)
    (sourcePoint E p ≫ k)
    (by rw [Category.assoc, h.2.w, ← Category.assoc, outer_inner,
        Category.assoc, ← h.1, ← Category.assoc])
    (by rw [Category.assoc, h.2.w, ← Category.assoc, inner_source,
        Category.assoc, w, ← Category.assoc])

@[reassoc (attr := simp)]
lemma composableMap_outerArrow :
    composableMap h p q k w ≫ outerArrow F q = outerArrow E p ≫ g :=
  composableLift_outerArrow _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma composableMap_innerArrow :
    composableMap h p q k w ≫ innerArrow F q = innerArrow E p ≫ g :=
  composableLift_innerArrow _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma composableMap_sourcePoint :
    composableMap h p q k w ≫ sourcePoint F q = sourcePoint E p ≫ k :=
  composableLift_sourcePoint _ _ _ _ _ _ _

variable {h p q k w}

/-- A compatible pair of prospective action maps has compatible evaluations. -/
lemma evaluation_naturality
    (a : pullback E.s p ⟶ P) (b : pullback F.s q ⟶ Q)
    (hw : a ≫ k = arrowMap h p q k w ≫ b)
    {T : Scheme.{u}} (r : T ⟶ E.R) (v : T ⟶ P)
    (hrv : r ≫ E.s = v ≫ p) :
    (pullback.lift r v hrv ≫ a) ≫ k =
      pullback.lift (r ≫ g) (v ≫ k)
        (by rw [Category.assoc, h.2.w, ← Category.assoc, hrv,
          Category.assoc, w, ← Category.assoc]) ≫ b := by
  rw [Category.assoc, hw, ← Category.assoc]
  apply congrArg (· ≫ b)
  apply pullback.hom_ext <;>
    simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

/-- Naturality of the unit equation, before assuming either unit law. -/
lemma unit_equation_naturality
    (a : pullback E.s p ⟶ P) (b : pullback F.s q ⟶ Q)
    (hw : a ≫ k = arrowMap h p q k w ≫ b) :
    (unitInput p ≫ a) ≫ k = k ≫ unitInput q ≫ b := by
  rw [Category.assoc, hw, ← Category.assoc, unitInput_arrowMap, Category.assoc]

/-- Naturality of successive actions, before assuming associativity. -/
lemma successive_naturality
    (a : pullback E.s p ⟶ P) (ha : a ≫ p = pullback.fst E.s p ≫ E.t)
    (b : pullback F.s q ⟶ Q) (hb : b ≫ q = pullback.fst F.s q ≫ F.t)
    (hw : a ≫ k = arrowMap h p q k w ≫ b) :
    successive a ha ≫ k = composableMap h p q k w ≫ successive b hb := by
  dsimp only [successive]
  rw [evaluation_naturality a b hw]
  simp only [← Category.assoc]
  apply congrArg (· ≫ b)
  apply pullback.hom_ext
  · simp [pullback.lift_fst]
  · simp only [Category.assoc, pullback.lift_snd]
    simp only [← Category.assoc]
    rw [evaluation_naturality a b hw]
    apply congrArg (· ≫ b)
    apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd]

/-- Naturality of action by the composite, before assuming associativity. -/
lemma composite_naturality
    (a : pullback E.s p ⟶ P) (b : pullback F.s q ⟶ Q)
    (hw : a ≫ k = arrowMap h p q k w ≫ b) :
    composite a ≫ k = composableMap h p q k w ≫ composite b := by
  dsimp only [composite]
  rw [evaluation_naturality a b hw]
  simp only [← Category.assoc]
  apply congrArg (· ≫ b)
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, h.compose_naturality]
    apply F.hom_ext <;> simp
  · simp [pullback.lift_snd]

/-- Both sides of the universal associativity equation lie over the target
of the outer arrow. -/
lemma successive_over
    (a : pullback E.s p ⟶ P) (ha : a ≫ p = pullback.fst E.s p ≫ E.t) :
    successive a ha ≫ p = outerArrow E p ≫ E.t := by
  dsimp only [successive]
  rw [Category.assoc, ha, pullback.lift_fst_assoc]

lemma composite_over
    (a : pullback E.s p ⟶ P) (ha : a ≫ p = pullback.fst E.s p ≫ E.t) :
    composite a ≫ p = outerArrow E p ≫ E.t := by
  dsimp only [composite]
  rw [Category.assoc, ha, pullback.lift_fst_assoc, compose_t]

/-- The unit expression lies over the same object as the identity. -/
lemma unit_equation_over
    (a : pullback E.s p ⟶ P) (ha : a ≫ p = pullback.fst E.s p ≫ E.t) :
    (unitInput p ≫ a) ≫ p = p := by
  rw [Category.assoc, ha, unitInput_fst_assoc, unit_t,
    Category.comp_id]

/-- In a pullback square of action objects, it suffices to verify the two
finite law equations after mapping to the lower object scheme. -/
noncomputable def ofEquationsAfterMap
    (hp : IsPullback k p q f)
    (a : pullback E.s p ⟶ P) (ha : a ≫ p = pullback.fst E.s p ≫ E.t)
    (hu : (unitInput p ≫ a) ≫ k = k)
    (hc : successive a ha ≫ k = composite a ≫ k) : Action E p :=
  ofAssociative a ha
    (by
      apply hp.hom_ext
      · simpa only [unitInput, Category.id_comp] using hu
      · simpa only [unitInput, Category.id_comp] using unit_equation_over a ha)
    (by
      apply hp.hom_ext
      · exact hc
      · rw [successive_over a ha, composite_over a ha])

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action
