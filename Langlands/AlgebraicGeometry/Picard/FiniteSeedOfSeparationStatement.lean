import Langlands.AlgebraicGeometry.Picard.FiniteSectionSeed
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite section seeds from pointwise separation on a Noetherian scheme

On a Noetherian scheme over a field, if each rational point other than `z` and each nonzero
rational tangent vector at `z` is detected by some global line-bundle section that vanishes
at `z` and is nonzero at some rational point, then finitely many such sections form a finite
point-tangent section seed at `z`. This module supplies a statement target, not a proof.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

/-- Let `X` be a Noetherian scheme with a morphism `p` to the spectrum of a field `K`, and
`z : Spec K ⟶ X`. Suppose that every rational point `x ≠ z` and every nonzero rational
tangent vector `t` at `z` is detected (the section does not vanish along it) by a global
section of some line bundle that vanishes along `z` and does not vanish along some rational
point. Then there is a finite family of such sections, indexed by `Fin n`, forming a finite
point-tangent section seed at `z`. The size `n` may be zero.
This proposition is a statement target, not a proof. -/
def FiniteSeedOfSeparationStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) (z : Spec (CommRingCat.of K) ⟶ X),
    (∀ x : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p x → x ≠ z →
      ∃ (L : LineBundle X) (s : GlobalSections L.obj),
        VanishesAlong L z s ∧
          (∃ y : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p y ∧ ¬ VanishesAlong L y s) ∧
          ¬ VanishesAlong L x s) →
    (∀ t : Spec (CommRingCat.of (DualNumber K)) ⟶ X, IsNonzeroTangentVectorAt p z t →
      ∃ (L : LineBundle X) (s : GlobalSections L.obj),
        VanishesAlong L z s ∧
          (∃ y : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p y ∧ ¬ VanishesAlong L y s) ∧
          ¬ VanishesAlong L t s) →
    ∃ (n : ℕ) (L : Fin n → LineBundle X) (s : (i : Fin n) → GlobalSections (L i).obj),
      IsFinitePointTangentSectionSeed p z n L s

end Langlands.AlgebraicGeometry.Picard
