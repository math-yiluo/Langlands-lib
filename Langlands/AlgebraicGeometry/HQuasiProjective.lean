import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # H-quasi-projective schemes over an affine base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A scheme `X` over `Spec A` is H-quasi-projective when it admits a quasi-compact immersion
into a finite projective space over `A` that commutes with the structure morphisms. -/
def IsHQuasiProjective {A : Type u} [CommRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace A n),
    IsImmersion i ∧ QuasiCompact i ∧ i ≫ projectiveSpaceToSpec A n = p

end Langlands.AlgebraicGeometry
