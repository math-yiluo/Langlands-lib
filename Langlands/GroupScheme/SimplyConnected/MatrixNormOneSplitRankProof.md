# Split rank of `SL_m(D)`: proof

Authors: Worker 161, Worker 31.

`Langlands.GroupScheme.CentralSimpleUnits.matrixNormOneSplitRank` proves the unchanged
published `Langlands.GroupScheme.CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u}`
from `Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankStatement`. It holds for
arbitrary universe `u`. Its type is exactly that proposition, and it has no hypotheses.

The proposition says the following. Let `K : Type u` be any field and `D : Type u` a
finite-dimensional central division `K`-algebra. Let `m` be a natural number with
`[NeZero m]`. Then `splitRank (normOne K (Matrix (Fin m) (Fin m) D))` equals
`((m - 1 : ℕ) : ℕ∞)`. Here `normOne` is the actual reduced-norm-one group scheme of
`Langlands.GroupScheme.CentralSimpleNormOne`. `splitRank` is the supremum of `Nat.card I`
over closed split tori `splitTorus (Spec K) I ⟶ G` with `I` finite. The field may have
any characteristic and may be finite. The cases `m = 1` and `D = K` are included.

## Implemented proof

After introducing `K`, `D`, their instances and `m`, the proof is `le_antisymm` of two
inequalities, each proved in its own helper module of this contribution.

1. **Upper bound**, `Langlands.GroupScheme.MatrixNormOneSplitRank.splitRank_le` in
   `Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankUpper` (Worker 161):
   `splitRank (normOne K (Matrix (Fin m) (Fin m) D)) ≤ m - 1`. Let `𝔾ₘ^I` be a closed
   split torus in `SL_m(D)`. The inverse of its universal point over `K[ℤ^I]` is
   `∑ₘ Xᵐ ⊗ eₘ`, where `m` runs over the weights of the inverse-right-regular
   representation. The `eₘ` are nonzero orthogonal idempotents with sum `1`, and the
   weights generate `ℤ^I`. Reduced norm one gives the relation `∑ₘ dim(eₘ A) · m = 0`.
   Each right ideal `eₘ M_m(D)` has dimension at least `m · dim D`, so there are at most
   `m` weights, and `|I| ≤ m - 1`. The linear algebra is in
   `Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankAlgebra`. The argument
   uses the universal point rather than rational points, so finite fields are covered.

2. **Lower bound**, `Langlands.GroupScheme.CentralSimpleUnits.sub_one_le_splitRank_normOne`
   in `Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankLower` (Worker 31):
   `m - 1 ≤ splitRank (normOne K (Matrix (Fin m) (Fin m) D))`. The diagonal torus
   `t ↦ diag((t₁ ⋯ t_{m-1})⁻¹, t₁, …, t_{m-1})` has reduced norm one, by a
   permutation-conjugation argument. It is a monomorphism, hence a closed subgroup, of
   dimension `m - 1`.

The paired Markdown files of the three helper modules describe their proofs in detail.

## Scope and dependencies

The proof adds no premise, axiom or proof hole. The development check reports only the
axioms `propext`, `Classical.choice` and `Quot.sound`. The import closure of this module
contains no module of the local rank-one classification or of local Kneser–Tits. No
result whose planned proof consumes this rank computation is used.
