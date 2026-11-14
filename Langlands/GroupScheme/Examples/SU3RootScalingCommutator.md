# Scaling commutators in quadratic unitary root coordinates

This module defines
`Langlands.GroupScheme.SU3Root.Parameters.scalingCommutatorCentral`
and proves its factorization and filtration bounds. It is an internal
coordinate construction used by the positive-depth torus-root calculation
of Task 6194. It does not construct coordinates for a reductive group or
identify their depths with a supplied apartment.

## Definition and conventions

For a commutative ring `A`, an involution `c : RingInvolution A`,
`a : A`, and `p : Parameters c`, write `δ = a - 1` and `p = (α, β)`.
The correction is the literal central parameter

`scalingCommutatorCentral a p = (0, bar(δ)β - δ bar(β))`.

Its second coordinate has trace zero, so its first coordinate zero defines
an element of `Parameters.central c`. The construction works at arbitrary
universe `u`. No invertibility of `a` is assumed.

The Library group law has cross term `first₁ * bar(first₂)`, and inverse
`(α, β)⁻¹ = (-α, bar(β))`. With `Parameters.scale` from
`SU3RootScaling`, the theorem `scale_mul_inv_factorization` proves

`scale a p * p⁻¹ = scale δ p * (scalingCommutatorCentral a p).val`.

The proof expands both coordinates. Equality of the second coordinates is
a polynomial consequence of the defining trace-norm relation
`β + bar(β) = α bar(α)`.

## Valuation bounds

Let `L` be a field, let `omega : AddValuation L (WithTop ℝ)`, and assume
`omega (bar z) = omega z` for every `z : L`. All thresholds below are
arbitrary real numbers; infinity is retained throughout.

If `r ≤ omega (a - 1)` and `p ∈ Parameters.filtration omega hinv s`, then:

- `scale_sub_one_mem_filtration` places `scale (a - 1) p` in the root
  filtration of depth `r + s`, by the published `Parameters.depthA_scale`.
- `scalingCommutatorCentral_mem` places the correction in the literal
  central filtration of depth `r + 2*s`. Both terms of its second
  coordinate have this bound by multiplicativity and involution
  invariance; the valuation inequality for subtraction combines them.
- `scale_mul_inv_mem_filtration_product` packages the two factors and
  their equality as an existential product decomposition.

If additionally `0 ≤ omega a`, `norm_sub_one_ge` proves
`r ≤ omega (a * bar(a) - 1)` from the same scalar congruence. It expands
this difference as `(a - 1) * bar(a) + bar(a - 1)` and bounds both terms.
For `p` in the central filtration at depth `s`,
`scale_mul_inv_mem_centralFiltration` then places the whole commutator in
the central filtration at depth `r + s`. Its second coordinate is
`(a * bar(a) - 1) * β`, by the trace-zero equation for `p`.

These real-threshold estimates allow an apartment translation before a
consumer uses nonnegative depth: the root threshold shifts once and the
central threshold twice. The final comparison `r + 2*s ≥ r + s` requires
`s ≥ 0` and is not asserted for arbitrary real `s` here.

## Provenance

The definition and lemmas are derived internal algebra on the existing
Library coordinate group, following the coordinate calculation explained
in `KPLocalTorusRootCommutatorStatement.md` with the implemented group-law
convention. The only substantive imported coordinate results are
`Parameters.equation`, `Parameters.scale`, `Parameters.depthA_scale`, and
the root and central filtration membership descriptions. The proofs add
no source theorem or hypothesis asserting a building property.
