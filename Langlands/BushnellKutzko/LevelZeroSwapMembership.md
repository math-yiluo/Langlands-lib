# Two-block membership in the standard unit groups

For blocks `i < j`, the module tests membership of a two-block element
embedded by `pairGL` in `J0 = U(𝔄)` or `J1 = U^1(𝔄)`.
[Standard order](LevelZeroStandard.md)

- `Is2Ord` requires that all four blocks be integral and the upper right
  block lie in the maximal ideal. `Is2Rad` also requires that both diagonal
  blocks reduce to the identity.
- `pairEmb_forall` reduces an entrywise condition on the embedded matrix
  to tests on the four blocks and the identity on the remaining indices.
  The subgroup criteria `pairGL_mem_J0` and `pairGL_mem_J1` use `Is2Ord`
  and `Is2Rad` respectively on the two-block element and its inverse.
- `lowerU_mem_J1` and `upperU_mem_J1` give the tests for lower integral and
  upper maximal-ideal entries. `diagU_mem_J0` applies to block diagonal
  elements with integral blocks and integral inverses.

The inverse formulas for `lowerU`, `upperU` and `diagU` follow by direct
matrix multiplication.
