import Mathlib.RingTheory.Regular.RegularSequence

/-! # Powers of a regular sequence -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Algebra Lemma 10.68.9 (07DV): let `M` be an `R`-module, `f₁, …, f_r ∈ R` and
`e₁, …, e_r > 0`. Then `f₁, …, f_r` is an `M`-regular sequence if and only if
`f₁^{e₁}, …, f_r^{e_r}` is an `M`-regular sequence. -/
def RegularSequencePowersStatement : Prop :=
  ∀ (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] (r : ℕ) (f : Fin r → R)
    (e : Fin r → ℕ), (∀ i, 0 < e i) →
    (RingTheory.Sequence.IsRegular M (List.ofFn f) ↔
      RingTheory.Sequence.IsRegular M (List.ofFn fun i => f i ^ e i))

end Langlands.CommutativeAlgebra.Popescu
