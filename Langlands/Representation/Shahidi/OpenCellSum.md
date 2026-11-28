# Summation by depth

Module `Langlands.Representation.Shahidi.OpenCellSum`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `summable_of_depth_bound`: a function on a type with an `ℕ`-valued depth whose fibres are
  finite with at most `N(D)` elements, and with `‖F y‖ ≤ C ρ^(depth y)` for some `C, ρ ≥ 0`, is
  summable when `∑_D N(D) C ρ^D` converges.
- `hasSum_of_depth_fibers`: if each fibre sums to `g(D)`, `g` sums to `P`, and the whole function
  is summable, then the whole sum is `P`.
- `openCellSummand K ψ f Y = f(w u'(Y)) conj ψ(Y_(t,0))`: the summand of the target statement.
- `paramBound`, `summandConstant`, `summandRatio`: explicit constants; `norm_openCellSummand_le`:
  for `ψ` of conductor `𝒪`, a function `f` with the target transformation law
  (`IsOpenCellSection`) and the bounds `‖a_i‖ ≤ q^A`, `‖c_j⁻¹‖ ≤ q^B`, the summand of depth `D` is
  bounded by
  `summandConstant · summandRatio^D`, with `summandRatio = q^(-Re s) · (explicit factor)`.
- `isIntegrallyTrivial_of_additiveConductor`: a character of conductor `𝒪` gives a standard
  character trivial on integral unipotents.

## Provenance

Derived; it implements the estimate described in the Markdown of
`Langlands.Shahidi.UnramifiedOpenCellSumStatement` (comparison with the source, uniformity of
the half-plane).
