import Langlands.AlgebraicGeometry.ProjectiveSpace

/-! # The finite affine coordinate cover of polynomial projective space -/

universe u

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- For every commutative ring `R : Type u` and every `n : ℕ`, each actual coordinate open
`D₊(X i)` of the polynomial-Proj projective space `ProjectiveSpace R n` is an affine open,
these `n + 1` opens have supremum `⊤`, and the underlying space of `ProjectiveSpace R n` is
compact. No hypothesis is placed on `R` or `n`. This proposition is a statement target, not
a proof of these properties. -/
def ProjectiveSpaceCoordinateCoverStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    (∀ i : Fin (n + 1), IsAffineOpen (projectiveSpaceCoordinateOpen R n i)) ∧
    (⨆ i : Fin (n + 1), projectiveSpaceCoordinateOpen R n i) = ⊤ ∧
    CompactSpace (ProjectiveSpace R n)

end Langlands.AlgebraicGeometry
