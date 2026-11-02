import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.CategoryTheory.Retract

/-! # Cohomology retraction along a finite flat morphism of invertible rank -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- Over a field `K`, let `f : X ⟶ Y` be a morphism of `K`-schemes that is finite, flat and
locally of finite presentation, of constant rank `d` with `(d : K) ≠ 0`. Then for every
quasi-coherent `M` on `Y` and every `n`, the `K`-module `Hⁿ(Y, M)` is a retract of
`Hⁿ(X, f^* M)`. -/
def FiniteFlatCohomologyRetractStatement : Prop :=
  ∀ (K : Type u) [Field K] (X Y : Over (Spec (CommRingCat.of K))) (f : X ⟶ Y),
    IsFinite f.left → Flat f.left → LocallyOfFinitePresentation f.left →
      ∀ d : ℕ, (d : K) ≠ 0 → (∀ y : Y.left, f.left.finrank y = d) →
        ∀ (M : Y.left.Modules), M.IsQuasicoherent → ∀ n : ℕ,
          Nonempty (Retract ((DerivedSections.relativeCohomology Y.hom n).obj M)
            ((DerivedSections.relativeCohomology X.hom n).obj
              ((Scheme.Modules.pullback f.left).obj M)))

end Langlands.AlgebraicGeometry.Modules
