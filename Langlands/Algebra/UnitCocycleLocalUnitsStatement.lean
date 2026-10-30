import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Local unit generators for a unit cocycle along a faithfully flat algebra -/

universe u

open scoped TensorProduct

namespace Langlands.Algebra

/-- Let `R → S` be faithfully flat and let `u` be a unit of `S ⊗[R] S`, with inverse `v`,
satisfying the cocycle identity `u₁₃ = u₂₃ * u₁₂` in `S ⊗[R] (S ⊗[R] S)`. Then the elements
`r : R` whose image in `S` is a product `m * m'`, where `u * (m ⊗ 1) = 1 ⊗ m` and
`v * (m' ⊗ 1) = 1 ⊗ m'`, generate the unit ideal of `R`. -/
def UnitCocycleLocalUnitsStatement : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (u v : S ⊗[R] S), u * v = 1 →
    Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) u =
      (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) u *
        Algebra.TensorProduct.map (AlgHom.id R S)
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) u →
    Ideal.span {r : R | ∃ m m' : S, u * (m ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m ∧
      v * (m' ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m' ∧ algebraMap R S r = m * m'} = ⊤

end Langlands.Algebra
