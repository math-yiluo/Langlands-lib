import Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction

/-!
# The linked Jacquet functional for two interlaced induction blocks

The statement `RealInterlacedInducedInducedLinkedJacquetFunctionalStatement` is the case of
`RealInducedInducedLinkedJacquetFunctionalStatement` (module `RealLinkedJacquetPairReduction`)
in which the two linked induction blocks are interlaced or touch. It is proved in
`RealInterlacedMirror`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- **Two interlaced linked induction blocks.** Let `d`, `e` be induction blocks of nonzero
weights `m`, `m'` with `t(d) - t(e) = ||m| - |m'||/2 + k` and `1 ≤ k ≤ min(|m|, |m'|)`. Then the
standard module of `[d, e]` on `GL₄(ℝ)` carries a functional as in
`RealLinkedJacquetFunctionalExists`. With `(u, v) = (t + |m|/2, t - |m|/2)` for each block,
these are the linked pairs with `v(e) < v(d) ≤ u(e) < u(d)`. -/
def RealInterlacedInducedInducedLinkedJacquetFunctionalStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ), d.weight ≠ 0 → e.weight ≠ 0 → 0 < k →
    k ≤ min d.weight.natAbs e.weight.natAbs →
    d.exponent - e.exponent =
      ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℕ) : ℂ) / 2 + k →
    RealLinkedJacquetFunctionalExists 4 [RealBlock.induced d, RealBlock.induced e]

end Langlands.Archimedean
