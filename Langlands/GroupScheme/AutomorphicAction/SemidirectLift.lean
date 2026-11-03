import Langlands.GroupScheme.AutomorphicAction.EquivariantSemidirectMap

/-! # Lifting a commuting action to an actual semidirect product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {K L G : GroupScheme B}
    (a : AutomorphicAction K G) (b : AutomorphicAction L G)

/-- The coordinate morphism acts on the normal factor and fixes the acting
factor. The commuting-action hypothesis is needed for its group laws. -/
def semidirectLiftHom : L.X ⊗ a.semidirectProduct.X ⟶ a.semidirectProduct.X :=
  lift
    (b.act (fst L.X a.semidirectProduct.X)
      (snd L.X a.semidirectProduct.X ≫ fst G.X K.X))
    (snd L.X a.semidirectProduct.X ≫ snd G.X K.X)

set_option backward.isDefEq.respectTransparency.types false in
theorem lift_semidirectLiftHom {T : Over B}
    (s : T ⟶ L.X) (z : T ⟶ a.semidirectProduct.X) :
    lift s z ≫ semidirectLiftHom a b =
      lift (b.act s (z ≫ fst G.X K.X)) (z ≫ snd G.X K.X) := by
  change (lift s z ≫ semidirectLiftHom a b : T ⟶ G.X ⊗ K.X) = _
  simp only [semidirectLiftHom, comp_lift, naturality, lift_fst,
    ← Category.assoc, lift_snd]

/-- On every test, the lifted coordinate map leaves the acting coordinate
unchanged and applies the external action to the normal coordinate. -/
theorem semidirectLiftHom_points {T : Over B}
    (s : T ⟶ L.X) (z : T ⟶ a.semidirectProduct.X) :
    a.semidirectPointsEquiv T (lift s z ≫ semidirectLiftHom a b) =
      ⟨b.act s (a.semidirectPointsEquiv T z).left,
        (a.semidirectPointsEquiv T z).right⟩ := by
  rw [lift_semidirectLiftHom, semidirectPointsEquiv_lift]
  rfl

/-- An action commuting with the inner action lifts to the semidirect group
scheme, with trivial action on its acting factor. -/
def semidirectLift
    (hcomm : ∀ (T : Over B) (s : T ⟶ L.X) (k : T ⟶ K.X) (g : T ⟶ G.X),
      b.act s (a.act k g) = a.act k (b.act s g)) :
    AutomorphicAction L a.semidirectProduct where
  hom := semidirectLiftHom a b
  one_left z := by
    apply (a.semidirectPointsEquiv _).injective
    rw [semidirectLiftHom_points]
    apply SemidirectProduct.ext
    · exact b.act_one_left _
    · rfl
  mul_left s t z := by
    apply (a.semidirectPointsEquiv _).injective
    rw [semidirectLiftHom_points, semidirectLiftHom_points,
      semidirectLiftHom_points]
    apply SemidirectProduct.ext
    · exact b.act_mul_left _ _ _
    · rfl
  mul_right s z w := by
    apply (a.semidirectPointsEquiv _).injective
    simp only [semidirectLiftHom_points, map_mul]
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, pointsAction_apply,
        b.act_mul_right, hcomm]
    · rfl

variable
    (hcomm : ∀ (T : Over B) (s : T ⟶ L.X) (k : T ⟶ K.X) (g : T ⟶ G.X),
      b.act s (a.act k g) = a.act k (b.act s g))

/-- The constructed action has the expected coordinates on all schemes over
the base, including nonreduced tests. -/
theorem semidirectLift_act_points {T : Over B}
    (s : T ⟶ L.X) (z : T ⟶ a.semidirectProduct.X) :
    a.semidirectPointsEquiv T ((semidirectLift a b hcomm).act s z) =
      ⟨b.act s (a.semidirectPointsEquiv T z).left,
        (a.semidirectPointsEquiv T z).right⟩ :=
  semidirectLiftHom_points a b s z

/-- The normal inclusion intertwines the original and lifted external actions. -/
theorem semidirectLift_inl {T : Over B} (s : T ⟶ L.X) (g : T ⟶ G.X) :
    (semidirectLift a b hcomm).act s (g ≫ a.semidirectInl.hom.hom) =
      b.act s g ≫ a.semidirectInl.hom.hom := by
  apply (a.semidirectPointsEquiv T).injective
  rw [semidirectLift_act_points, semidirectInl_points, semidirectInl_points]
  rfl

/-- Every acting-factor point is fixed by the lifted external action. -/
theorem semidirectLift_inr {T : Over B} (s : T ⟶ L.X) (k : T ⟶ K.X) :
    (semidirectLift a b hcomm).act s (k ≫ a.semidirectInr.hom.hom) =
      k ≫ a.semidirectInr.hom.hom := by
  apply (a.semidirectPointsEquiv T).injective
  rw [semidirectLift_act_points, semidirectInr_points]
  apply SemidirectProduct.ext
  · exact b.act_one s
  · rfl

/-- The projection to the acting factor is invariant under the external action. -/
theorem semidirectLift_projection {T : Over B}
    (s : T ⟶ L.X) (z : T ⟶ a.semidirectProduct.X) :
    (semidirectLift a b hcomm).act s z ≫ a.semidirectProjection.hom.hom =
      z ≫ a.semidirectProjection.hom.hom := by
  rw [semidirectProjection_points, semidirectProjection_points,
    semidirectLift_act_points]

section EquivariantMap

variable {H : GroupScheme B}
    (c : AutomorphicAction K H) (d : AutomorphicAction L H)
    (hcommH : ∀ (T : Over B) (s : T ⟶ L.X) (k : T ⟶ K.X) (h : T ⟶ H.X),
      d.act s (c.act k h) = c.act k (d.act s h))
    (f : H ⟶ G)
    (hinner : ∀ (T : Over B) (k : T ⟶ K.X) (h : T ⟶ H.X),
      c.act k h ≫ f.hom.hom = a.act k (h ≫ f.hom.hom))
    (houter : ∀ (T : Over B) (s : T ⟶ L.X) (h : T ⟶ H.X),
      d.act s h ≫ f.hom.hom = b.act s (h ≫ f.hom.hom))

include houter in
/-- The canonical semidirect map also intertwines the lifted commuting actions. -/
theorem semidirectMap_semidirectLift {T : Over B}
    (s : T ⟶ L.X) (z : T ⟶ c.semidirectProduct.X) :
    (semidirectLift c d hcommH).act s z ≫
        (semidirectMap c a f hinner).hom.hom =
      (semidirectLift a b hcomm).act s
        (z ≫ (semidirectMap c a f hinner).hom.hom) := by
  apply (a.semidirectPointsEquiv T).injective
  rw [semidirectMap_points, semidirectLift_act_points,
    semidirectLift_act_points, semidirectMap_points]
  apply SemidirectProduct.ext
  · exact houter T s _
  · rfl

end EquivariantMap

end Langlands.GroupScheme.AutomorphicAction
