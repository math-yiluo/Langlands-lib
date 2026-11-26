# Traces of finite block operators with finite-rank entries

Module `Langlands.BaseChange.TwistedVanDijk.BlockTrace`, in the namespace
`Langlands.FiniteRankEnd`. It extends the finite-rank trace of
`Langlands.LinearAlgebra.FiniteRankTrace` to block operators on `X → V`, for a finite index
type `X` and a complex vector space `V` of any dimension.

## Contents

- `blockEntryMap x y T` is the linear map `ι_x ∘ T ∘ π_y` of `X → V`, sending `f` to the
  function equal to `T (f y)` at `x` and to `0` elsewhere (`blockEntryMap_apply`).
  `blockEntryMap_mem`: it has finite rank when `T` does. `blockEntry x y T` is the same map as
  an element of `finiteRankEnd (X → V)`.
- `trace_blockEntry`: the trace of `blockEntry x y T` is `trace T` when `x = y` and `0`
  otherwise.
- `blockOperator K`, for `K : X → X → finiteRankEnd V`, is `∑ x, ∑ y, blockEntry x y (K x y)`,
  the operator `f ↦ (x ↦ ∑ y, K x y (f y))` (`blockOperator_apply`).
- `trace_blockOperator`: `trace (blockOperator K) = ∑ x, trace (K x x)`.

## Proofs

`blockEntryMap x y T` is `ι_x ∘ T ∘ π_y`; composing a map with Noetherian range on either side
keeps the range Noetherian, which is the finite-rank condition.

For `trace_blockEntry`, factor `blockEntry x y T` as `g ∘ f` with
`f = T.rangeRestrict ∘ π_y : (X → V) → range T` and `g = ι_x ∘ (range T).subtype`. The
Library's `trace_eq_of_factorization` gives `trace (g ∘ f) = trace (f ∘ g)` on the
finite-dimensional space `range T`. When `x = y`, `f ∘ g` is the restriction of `T` to its
range, whose trace is `trace T` (the definition of the finite-rank trace through
`onSubspace`); when `x ≠ y`, `π_y ∘ ι_x = 0`, so `f ∘ g = 0`.

`trace_blockOperator` follows by additivity of the trace and `Finset.sum_ite_eq`.
`blockOperator_apply` evaluates the double sum pointwise: only the term with first index `x`
survives at `x`.
