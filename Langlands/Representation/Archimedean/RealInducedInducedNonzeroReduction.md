# Removing weight-zero blocks from the two-induced-block filtration problem

Worker 769, Task 7135 (`d3276721-4799-4af9-8958-2f42c88102df`).
This is an internal reduction of the published filtration target. It uses the
concrete standard modules and their actual intertwiners modulo earlier ranges.
It makes no independent assertion about composition factors.

`RealInducedInducedNonzeroFiltrationStatement` is the restriction of
`RealInducedInducedFiltrationStatement` to data `d`, `e` whose integer weights
are both nonzero. It retains the strict inequality
`realBlockExponent (.induced d) < realBlockExponent (.induced e)` and concludes
`RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)`.

`RealInducedInducedFromNonzeroReductionStatement` says that the following
three premises imply the full, unrestricted two-induced-block statement:

- `RealCharacterInducedFiltrationStatement`, the character–induced case on
  `GL₃(ℝ)`;
- `RealInducedCharacterFiltrationStatement`, the induced–character case on
  `GL₃(ℝ)`;
- `RealInducedInducedNonzeroFiltrationStatement`.

The theorem `realInducedInducedFromNonzeroReduction` proves this implication.
It does not prove any of these three premises, and therefore does not by itself
complete Task 7135.

For a block `d` of weight zero and exponent `t`, the published zero-weight
expansion identifies its standard module with that of the two character blocks
`first d = sgn |·|^t` and `second d = |·|^t`. The fusion lemmas in
`RealInducedPairWeightZero` combine two character steps into a step past this
induction block, retaining the allowed-piece conditions, intertwiners modulo
earlier ranges, and spanning property.

The helper `RealInducedInducedNonzeroReduction.left_zero` assumes the first
`GL₃(ℝ)` premise and proves the desired filtration when `d.weight = 0`, for any
ambient rank `n` and lists `pre`, `post` of total rank
`realRank (pre ++ .induced d :: .induced e :: post) = n`. Induction in stages
places the character–induced filtration first between `second d` and `e`,
with `first d` in the prefix, then between `first d` and `e`, with `second d`
in the suffix. Both character exponents equal `d.exponent`, so the original
strict exponent inequality supplies both character-step inequalities.
`fuse_left` combines the two steps.

The helper `RealInducedInducedNonzeroReduction.right_zero` assumes the second
`GL₃(ℝ)` premise and proves the analogous result when `e.weight = 0`.
Induction in stages places the two induced–character steps between `d` and
`first e`, then between `d` and `second e`. The untouched character is in
the suffix for the first step and in the prefix for the second.
`fuse_right` combines them.

The final proof splits on `d.weight = 0`, then `e.weight = 0`. The first two
branches use these helpers at rank four with empty surrounding lists.
In the remaining branch both weights are nonzero, so the third premise applies
directly. No Langlands-classification theorem is used.
