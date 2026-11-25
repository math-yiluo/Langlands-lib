import Langlands.MathlibBase

/-! # Common affine neighbourhoods of finitely many points of codimension at most one -/

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.AlgebraicGeometry

/-- BLR, §6.4 Lemma 4: a finite set of points of codimension at most one
on a normal separated finite-type scheme over an affine noetherian base
has a common affine open neighbourhood. -/
def NormalCodimensionOneAffineNeighbourhoodStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R)),
    LocallyOfFiniteType p → QuasiCompact p → IsSeparated p →
    (∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) →
    ∀ E : Set X, E.Finite →
      (∀ x ∈ E, ringKrullDim (X.presheaf.stalk x) ≤ 1) →
      ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ U

end Langlands.AlgebraicGeometry
