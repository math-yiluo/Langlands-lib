import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAction

/-! # Action laws on a universal fibre product

Associativity of an action is a single equality of scheme morphisms.
This formulation is suitable for descent of finite presentation data.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

variable (E : EtaleEquivalenceRelation.{u}) {P : Scheme.{u}} (p : P ⟶ E.U)

/-- Composable original arrows together with a point over the last source. -/
noncomputable abbrev composable : Scheme.{u} :=
  pullback E.s (pullback.fst E.s p ≫ E.t)

/-- The first arrow in a composable action pair. -/
noncomputable def outerArrow : composable E p ⟶ E.R :=
  pullback.fst _ _

/-- The second arrow in a composable action pair. -/
noncomputable def innerArrow : composable E p ⟶ E.R :=
  pullback.snd _ _ ≫ pullback.fst E.s p

/-- The point on which the second arrow acts. -/
noncomputable def sourcePoint : composable E p ⟶ P :=
  pullback.snd _ _ ≫ pullback.snd E.s p

lemma outer_inner :
    outerArrow E p ≫ E.s = innerArrow E p ≫ E.t := by
  exact pullback.condition

lemma inner_source :
    innerArrow E p ≫ E.s = sourcePoint E p ≫ p := by
  dsimp only [innerArrow, sourcePoint]
  rw [Category.assoc, pullback.condition, ← Category.assoc]

/-- The universal compatible pair induced by two arrows and a point. -/
noncomputable def composableLift {T : Scheme.{u}} (r q : T ⟶ E.R) (v : T ⟶ P)
    (hrq : r ≫ E.s = q ≫ E.t) (hqv : q ≫ E.s = v ≫ p) :
    T ⟶ composable E p :=
  pullback.lift r (pullback.lift q v hqv)
    (by simpa only [← Category.assoc, pullback.lift_fst] using hrq)

@[reassoc (attr := simp)]
lemma composableLift_outerArrow {T : Scheme.{u}} (r q : T ⟶ E.R) (v : T ⟶ P)
    (hrq : r ≫ E.s = q ≫ E.t) (hqv : q ≫ E.s = v ≫ p) :
    composableLift E p r q v hrq hqv ≫ outerArrow E p = r :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma composableLift_innerArrow {T : Scheme.{u}} (r q : T ⟶ E.R) (v : T ⟶ P)
    (hrq : r ≫ E.s = q ≫ E.t) (hqv : q ≫ E.s = v ≫ p) :
    composableLift E p r q v hrq hqv ≫ innerArrow E p = q := by
  dsimp only [innerArrow, composableLift]
  rw [← Category.assoc, pullback.lift_snd, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma composableLift_sourcePoint {T : Scheme.{u}} (r q : T ⟶ E.R) (v : T ⟶ P)
    (hrq : r ≫ E.s = q ≫ E.t) (hqv : q ≫ E.s = v ≫ p) :
    composableLift E p r q v hrq hqv ≫ sourcePoint E p = v := by
  dsimp only [sourcePoint, composableLift]
  rw [← Category.assoc, pullback.lift_snd, pullback.lift_snd]

variable {E p}

/-- The two successive actions, on the universal composable-action scheme. -/
noncomputable def successive (a : pullback E.s p ⟶ P)
    (ha : a ≫ p = pullback.fst E.s p ≫ E.t) : composable E p ⟶ P :=
  pullback.lift (outerArrow E p)
    (pullback.lift (innerArrow E p) (sourcePoint E p) (inner_source E p) ≫ a)
    (by rw [Category.assoc, ha, ← Category.assoc, pullback.lift_fst]
        exact outer_inner E p) ≫ a

/-- The action of the composite, on the same universal scheme. -/
noncomputable def composite (a : pullback E.s p ⟶ P) : composable E p ⟶ P :=
  pullback.lift (E.compose (outerArrow E p) (innerArrow E p) (outer_inner E p))
    (sourcePoint E p) (by simpa using inner_source E p) ≫ a

/-- Associativity as one equality of morphisms from a fixed fibre product. -/
def Associative (a : pullback E.s p ⟶ P)
    (ha : a ≫ p = pullback.fst E.s p ≫ E.t) : Prop :=
  successive a ha = composite a

lemma associative_universal (A : Action E p) : Associative A.map A.over := by
  exact A.associative (outerArrow E p) (innerArrow E p) (sourcePoint E p)
    (outer_inner E p) (inner_source E p)

/-- It suffices to check associativity on the universal composable-action scheme. -/
noncomputable def ofAssociative (a : pullback E.s p ⟶ P)
    (ha : a ≫ p = pullback.fst E.s p ≫ E.t)
    (hu : pullback.lift (p ≫ E.unit) (𝟙 P) (by simp) ≫ a = 𝟙 P)
    (hc : Associative a ha) : Action E p where
  map := a
  over := ha
  unital := hu
  associative := by
    intro T r q v hrq hqv
    let z := composableLift E p r q v hrq hqv
    have hleft : z ≫ successive a ha =
        pullback.lift r (pullback.lift q v hqv ≫ a)
          (by rw [Category.assoc, ha, ← Category.assoc, pullback.lift_fst]; exact hrq) ≫
          a := by
      dsimp only [successive]
      rw [← Category.assoc]
      apply congrArg (· ≫ a)
      apply pullback.hom_ext
      · simp [z, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]
        apply congrArg (· ≫ a)
        apply pullback.hom_ext
        · simp [z, pullback.lift_fst]
        · simp [z, pullback.lift_snd]
    have hright : z ≫ composite a =
        pullback.lift (E.compose r q hrq) v (by simpa using hqv) ≫ a := by
      dsimp only [composite]
      rw [← Category.assoc]
      apply congrArg (· ≫ a)
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        apply E.hom_ext <;> simp [z]
      · simp [z, pullback.lift_snd]
    exact hleft.symm.trans ((congrArg (z ≫ ·) hc).trans hright)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action
