import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation

/-!
# Finite section seeds separating a point and its tangent vectors

A finite family of global sections of line bundles is a seed at a point `z` when every
section vanishes at `z`, every section is nonzero at some rational point, the sections
together detect every rational point other than `z`, and they together detect every
nonzero rational tangent vector at `z`. This is a section form of the finite family of
prime divisors in the first step of Milne's proof that abelian varieties are projective
(Abelian Varieties, Theorem 7.1, p.11). The definition asserts no existence.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The sections `s i` of the line bundles `L i`, indexed by `Fin n`, all vanish along
`z`; each is nonzero at some rational point; for every rational point `x ≠ z` some
section is nonzero at `x`; and for every nonzero rational tangent vector `t` at `z`
some section is nonzero along `t`. -/
def IsFinitePointTangentSectionSeed {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) (z : Spec (CommRingCat.of K) ⟶ X) (n : ℕ)
    (L : Fin n → LineBundle X)
    (s : (i : Fin n) → Langlands.SchemeModule.GlobalSections (L i).obj) : Prop :=
  (∀ i, VanishesAlong (L i) z (s i)) ∧
    (∀ i, ∃ y : Spec (CommRingCat.of K) ⟶ X,
      IsRationalPoint p y ∧ ¬ VanishesAlong (L i) y (s i)) ∧
    (∀ x : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p x → x ≠ z →
      ∃ i, ¬ VanishesAlong (L i) x (s i)) ∧
    (∀ t : Spec (CommRingCat.of (DualNumber K)) ⟶ X, IsNonzeroTangentVectorAt p z t →
      ∃ i, ¬ VanishesAlong (L i) t (s i))

end Langlands.AlgebraicGeometry.Picard
