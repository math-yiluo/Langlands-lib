import Langlands.AlgebraicGeometry.HQuasiProjective
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Quasi-compact projective immersions from an ample line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Stacks Lemma 29.40.3 (Tag 01VS) over an affine base. If a scheme `X` is locally of
finite type over `Spec R` and carries an ample line bundle, then `X` is H-quasi-projective
over `R`: it has a quasi-compact immersion into a finite projective space over `R` that
lies over the given structure morphism. This proposition is a statement, not a proof of
it. -/
def AmpleHQuasiProjectiveStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    LocallyOfFiniteType f → (∃ L : LineBundle X, L.IsAmple) → IsHQuasiProjective f

end Langlands.AlgebraicGeometry.Picard
