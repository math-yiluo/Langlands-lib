# Polynomial Northcott bound in a number field

`Langlands.Global.NumberFieldMulHeightCountStatement` is a proposition
definition. It supplies no proof.

## Statement

For every number field `K` (in any universe) there are a real constant `C`
and a natural exponent `M` such that for every real `B ≥ 1` the set
`{x ∈ K | mulHeight₁ x ≤ B}` has at most `C · B^M` elements. Here
`Height.mulHeight₁` is Mathlib's multiplicative Weil height of a field
element,
`H(x) = ∏_{v archimedean} max(|x|_v, 1)^{m_v} · ∏_{v finite} max(|x|_v, 1)`,
with the normalized absolute values of Mathlib's `InfinitePlace` and
`FinitePlace` and the local degrees `m_v`. The cardinality is `Set.ncard`.
The set is finite by Mathlib's `NumberField.finite_setOfPred_mulHeight₁_le`
(the Northcott property). This statement makes the count polynomial in `B`.

No asymptotic (Schanuel) formula and no optimal exponent is asserted.

## Provenance

Internal. Mathlib at the pinned commit proves only finiteness. The
polynomial bound is the elementary half of Northcott's theorem, and the
intended proof uses Mathlib's denominator bound
`NumberField.exists_nat_le_mulHeight₁`. It is needed to bound rational-point
counts in conjugated compact subsets of adelic groups, which controls the
growth of `R(f)φ` on `[G]`.

## Intended proof

A private proof compiles. An element `x` of height at most `B` has a
positive integer `n ≤ B` with `n x` integral
(`NumberField.exists_nat_le_mulHeight₁`). Every archimedean absolute value of
`x` is at most `H(x)`, so every archimedean absolute value of `a = n x` is at
most `B²`. Algebraic integers with all archimedean absolute values at most
`R` have integer coordinates, in an integral basis, bounded by `C₀ R`. This
holds because the coordinates are the image of the mixed embedding under the
inverse of Mathlib's `latticeBasis` (`latticeBasis_repr_apply`), a bounded
linear map. So there are at most `(2 C₀ R + 1)^d` of them, `d = [K : ℚ]`.
Summing over the at most `B` values of `n` gives the count
`(2 C₀ + 1)^d · B^{2d+1}`.
