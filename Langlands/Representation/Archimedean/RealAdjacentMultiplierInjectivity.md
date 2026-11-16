# Injectivity of adjacent block Fourier multipliers

Module `Langlands.Representation.Archimedean.RealAdjacentMultiplierInjectivity`.
The generic definitions and lemmas are in `Langlands.Archimedean.RealAdjacentMultiplier`;
the Frobenius-map applications are in `Langlands.Archimedean.RealBlockFrobeniusMap`.

This is internal infrastructure, derived from the ambient uncertainty theorem
`RealOrthogonalBlock.adjacent_uncertainty`, the standard-module Fourier conditions,
and the block Frobenius-map construction. There is no external literature assertion.

## Multiplier data

`CompactMultiplier n ds q μ` packages a complex-linear map from
`kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` to functions on
`GL_n(ℝ)`. On the compact group its `j`-th Fourier coefficient for the rotation at `q`
is `μ j` times the source coefficient. This structure asserts no existence of a map.
The selected definition `ofBlockFrobData h` packages the published `blockFrobMap h`
by composing with the inclusion of its target standard module into ambient functions.

## Injectivity criterion and proof

Let `p + 3 ≤ n`, and let `(r,s)` be either `(0,1)` or `(1,0)`.
For a multiplier at `p+s`, assume the source parity identity
`(-1)^ε = χ_(p+s)(-1) χ_(p+s+1)(-1)`. Let `m' < m` be natural cutoffs,
and assume `μ j ≠ 0` whenever `j-ε` is even and `m' ≤ |j|`.

`eq_zero_of_map_eq_zero` says that a kernel vector `f` is zero if its source Fourier
coefficients along `p+r` vanish for `|j| < m` at every point of `O(n)`.
Indeed, the multiplier identity makes its coefficients along `p+s` vanish for
`m' ≤ |j|` on the parity class. Coefficients of the other parity vanish by the
principal-series sign identity. The source function is continuous by its smoothness
and is right `O(n)`-finite by its membership. Ambient adjacent-rotation uncertainty
therefore makes it zero on `O(n)`, and principal-series equivariance makes it zero
on all of `GL_n(ℝ)`.

`injective_of_induced` applies this to the difference of two vectors. Its hypotheses
include `realInducedBlockAt ds (p+r) = some d` and `m' < d.weight.natAbs`.
The needed vanishing for `|j| < |d.weight|` is then part of source standard-module
membership. The theorem retains the parity identity and multiplier nonvanishing
hypotheses above.

## Frobenius-map application

`blockFrobMap_injective_of_adjacent_induced` applies this criterion to Frobenius data
`h : IsBlockFrobData n ds es (p+s) ε σ μ`, using its parity field.
`isRealStandardIntertwiner_blockFrobMap` converts the published intertwiner-modulo-zero
result into the standard intertwiner clauses by composing with the identity.
It assumes exactly the published multiplier recurrence with parameter
`realPositionExponent ds q - realPositionExponent ds (q+1) + 1`.

`injectiveIntertwinerExists_of_adjacent_induced` combines these two conclusions:
with Frobenius data, the adjacent induction block and strict cutoff bound,
nonvanishing on the parity class beyond that cutoff, and the recurrence, it gives
`RealInjectiveIntertwinerExists n ds es`.

These are conditional criteria. They neither construct Frobenius data for an exchanged
pair nor prove that a proposed multiplier satisfies its recurrence or nonvanishing
conditions. In particular, they do not establish `RealInducedSwapStatement`.
