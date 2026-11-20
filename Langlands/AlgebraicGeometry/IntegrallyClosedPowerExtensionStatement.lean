import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Extending sections whose power extends, on normal integral affine schemes (Milne 22.23) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Milne 2017, Lemma 22.23: let `X` be an integral affine scheme whose ring of global sections
is integrally closed, and let `U` be a nonempty (hence dense) open subscheme. If a section
`f ∈ O(U)` has a power `f ^ d` (`d ≥ 1`) that is the restriction of a global section, then `f`
itself is the restriction of a global section. -/
def IntegrallyClosedPowerExtensionStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsIntegral X] [IsAffine X], IsIntegrallyClosed Γ(X, ⊤) →
    ∀ (U : X.Opens), (U : Set X).Nonempty →
    ∀ (f : Γ(X, U)) (d : ℕ), 1 ≤ d →
      (∃ g : Γ(X, ⊤), X.presheaf.map (homOfLE le_top).op g = f ^ d) →
        ∃ h : Γ(X, ⊤), X.presheaf.map (homOfLE le_top).op h = f

end Langlands.AlgebraicGeometry
