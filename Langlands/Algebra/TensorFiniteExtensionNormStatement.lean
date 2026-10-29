import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Norm laws for tensoring with a finite field extension -/

universe u

open scoped TensorProduct

namespace Langlands.Algebra

/-- Derived algebraic norm laws for `A ⊗[K] L`, where `L / K` is a finite field extension and
`A` is any commutative `K`-algebra (internal support for the affine case of the norm of
Stacks 0BD2 along `X_L → X`). Mathlib's norm `Algebra.norm A : A ⊗[K] L →* A`, the
determinant of multiplication,
(1) commutes with base change along every `K`-algebra map `φ : A →ₐ[K] B`,
(2) sends `algebraMap A (A ⊗[K] L) a` to `a ^ Module.finrank K L`, and
(3) lies outside a prime `p` of `A` exactly when `f` lies outside every prime of `A ⊗[K] L`
over `p`.
This defines the statement only. -/
def TensorFiniteExtensionNormStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type u) [CommRing A] [Algebra K A],
    (∀ (B : Type u) [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (f : A ⊗[K] L),
        φ (Algebra.norm A f) =
          Algebra.norm B (Algebra.TensorProduct.map φ (AlgHom.id K L) f)) ∧
      (∀ a : A, Algebra.norm A (algebraMap A (A ⊗[K] L) a) = a ^ Module.finrank K L) ∧
      ∀ (f : A ⊗[K] L) (p : PrimeSpectrum A),
        Algebra.norm A f ∉ p.asIdeal ↔
          ∀ q : PrimeSpectrum (A ⊗[K] L),
            PrimeSpectrum.comap (algebraMap A (A ⊗[K] L)) q = p → f ∉ q.asIdeal

end Langlands.Algebra
