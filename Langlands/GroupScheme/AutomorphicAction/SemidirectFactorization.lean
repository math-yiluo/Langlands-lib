import Langlands.GroupScheme.AutomorphicAction.SemidirectLift
import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Recovering semidirect factorizations from actual subgroup multiplication -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {K N P : GroupScheme B}
    (a : AutomorphicAction K N) (i : N ⟶ P) (j : K ⟶ P)
    (ha : ∀ (T : Over B) (q : T ⟶ K.X) (n : T ⟶ N.X),
      a.act q n ≫ i.hom.hom =
        (q ≫ j.hom.hom) * (n ≫ i.hom.hom) * (q ≫ j.hom.hom)⁻¹)

/-- Multiply the two subgroup images using the supplied conjugation-compatible
inner action, on every test scheme. -/
def semidirectFactorPoints (T : Over B) :
    (T ⟶ a.semidirectProduct.X) →* (T ⟶ P.X) :=
  (SemidirectProduct.lift ((pointsMap i).app (op T)).hom
    ((pointsMap j).app (op T)).hom (by
      intro q
      apply MonoidHom.ext
      intro n
      exact ha T q n)).comp (a.semidirectPointsEquiv T).toMonoidHom

@[simp] theorem semidirectFactorPoints_apply (T : Over B)
    (z : T ⟶ a.semidirectProduct.X) :
    semidirectFactorPoints a i j ha T z =
      ((a.semidirectPointsEquiv T z).left ≫ i.hom.hom) *
        ((a.semidirectPointsEquiv T z).right ≫ j.hom.hom) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem semidirectFactorPoints_naturality {T V : Over B} (f : V ⟶ T)
    (z : T ⟶ a.semidirectProduct.X) :
    semidirectFactorPoints a i j ha V (f ≫ z) =
      f ≫ semidirectFactorPoints a i j ha T z := by
  simp only [semidirectFactorPoints_apply, semidirectPointsEquiv_left,
    semidirectPointsEquiv_right, MonObj.comp_mul, Category.assoc]

/-- The group-scheme homomorphism whose underlying scheme morphism is the
actual multiplication of the two supplied subgroup images. -/
def semidirectFactorHom : a.semidirectProduct ⟶ P :=
  homOfPoints (semidirectFactorPoints a i j ha)
    (semidirectFactorPoints_naturality a i j ha)

@[simp] theorem semidirectFactorHom_points {T : Over B}
    (z : T ⟶ a.semidirectProduct.X) :
    z ≫ (semidirectFactorHom a i j ha).hom.hom =
      ((a.semidirectPointsEquiv T z).left ≫ i.hom.hom) *
        ((a.semidirectPointsEquiv T z).right ≫ j.hom.hom) :=
  comp_homOfPoints _ _ T z

set_option backward.isDefEq.respectTransparency.types false in
/-- The constructed homomorphism uses precisely the supplied subgroup
multiplication map, with the normal factor first. -/
theorem semidirectFactorHom_hom :
    (semidirectFactorHom a i j ha).hom.hom = subgroupMultiplication i j := by
  have hp := semidirectFactorHom_points a i j ha (𝟙 a.semidirectProduct.X)
  rw [Category.id_comp] at hp
  calc
    _ = _ := hp
    _ = subgroupMultiplication i j := by
      change
        ((𝟙 (N.X ⊗ K.X) ≫ fst N.X K.X) ≫ i.hom.hom) *
          ((𝟙 (N.X ⊗ K.X) ≫ snd N.X K.X) ≫ j.hom.hom) =
            subgroupMultiplication i j
      rw [Category.id_comp, Category.id_comp]
      rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- A scheme multiplication isomorphism therefore gives an isomorphism of
actual group schemes with the supplied semidirect product. -/
def semidirectFactorIso [hmult : IsIso (subgroupMultiplication i j)] :
    a.semidirectProduct ≅ P := by
  let f := semidirectFactorHom a i j ha
  have : IsIso f.hom.hom := by
    dsimp only [f]
    rw [semidirectFactorHom_hom]
    exact hmult
  have : IsIso ((Mon.forget _).map f.hom) := ‹IsIso f.hom.hom›
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := ‹IsIso f.hom›
  have : IsIso f := isIso_of_reflects_iso _ (Grp.forget₂Mon _)
  exact asIso f

@[simp] theorem semidirectFactorIso_hom [IsIso (subgroupMultiplication i j)] :
    (semidirectFactorIso a i j ha).hom = semidirectFactorHom a i j ha := rfl

section ExternalAction

variable {L : GroupScheme B}
    (b : AutomorphicAction L P) (c : AutomorphicAction L N)
    (hi : ∀ (T : Over B) (s : T ⟶ L.X) (n : T ⟶ N.X),
      c.act s n ≫ i.hom.hom = b.act s (n ≫ i.hom.hom))
    (hj : ∀ (T : Over B) (s : T ⟶ L.X) (q : T ⟶ K.X),
      b.act s (q ≫ j.hom.hom) = q ≫ j.hom.hom)

include ha hi hj in
/-- An external action commutes with the inner action whenever it fixes the
acting subgroup and preserves the normal action through its monomorphism. -/
theorem semidirectFactor_commuting [Mono i.hom.hom]
    (T : Over B) (s : T ⟶ L.X) (q : T ⟶ K.X) (n : T ⟶ N.X) :
    c.act s (a.act q n) = a.act q (c.act s n) := by
  apply (cancel_mono i.hom.hom).mp
  rw [hi, ha, b.act_mul_right, b.act_mul_right, b.act_inv, hj, ha, hi]

include hi hj in
/-- The factor homomorphism intertwines the lifted external action with the
original action, retaining equality on every test scheme. -/
theorem semidirectFactorHom_equivariant
    (hcomm : ∀ (T : Over B) (s : T ⟶ L.X) (q : T ⟶ K.X) (n : T ⟶ N.X),
      c.act s (a.act q n) = a.act q (c.act s n))
    (T : Over B) (s : T ⟶ L.X) (z : T ⟶ a.semidirectProduct.X) :
    (a.semidirectLift c hcomm).act s z ≫ (semidirectFactorHom a i j ha).hom.hom =
      b.act s (z ≫ (semidirectFactorHom a i j ha).hom.hom) := by
  rw [semidirectFactorHom_points, semidirectLift_act_points,
    semidirectFactorHom_points, b.act_mul_right, hi, hj]

end ExternalAction

end Langlands.GroupScheme.AutomorphicAction
