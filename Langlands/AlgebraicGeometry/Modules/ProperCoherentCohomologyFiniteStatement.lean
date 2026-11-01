import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finiteness of actual proper coherent cohomology -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- Actual cohomology of a quasi-coherent sheaf with finite affine sections is
finite and eventually zero over a noetherian affine base when the map is proper. -/
def ProperCoherentCohomologyFiniteStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    IsProper f →
      ∀ (M : X.Modules), M.IsQuasicoherent →
        (∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(M, U.1)) →
          (∀ n : ℕ, Module.Finite R ((DerivedSections.relativeCohomology f n).obj M)) ∧
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            IsZero ((DerivedSections.relativeCohomology f n).obj M)

end Langlands.AlgebraicGeometry.Modules
