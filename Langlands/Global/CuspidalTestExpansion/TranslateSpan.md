# Spans of positive split translates

Module `Langlands.Global.CuspidalTestExpansion.TranslateSpan`
(namespace `Langlands.Global.StandardParabolicFamily`).

For a standard index `J` of a `StandardParabolicFamily`, the positive split component
`fam.positiveSplitComponent J` (the positive real points `𝔄_{P_J}` of the split component
`A_J` of `M_J`, as a subgroup of `P_J(𝔸)`) acts on functions on `G(𝔸)` by `fam.splitComponentRepresentation J`, the left
translations `f ↦ (g ↦ f(a g))` (`unnormalizedAction`). A local instance records that this
group is commutative (`positiveSplitComponent_mul_comm`).

## Declarations

- `translateSpan J f`: the complex span of the translates of `f` by
  `fam.positiveSplitComponent J`.
- `self_mem_translateSpan`: `f ∈ translateSpan J f`.
- `splitComponentRepresentation_mem_translateSpan`: the span is stable under the translations.
- `mem_translateSpan_of_sum`: if `c λ` (`λ ∈ s`, a finite set of complex parameters of `P_J`)
  has unnormalized exponent `λ` along `J` (`HasUnnormalizedExponent`), then each `c λ` lies in
  `translateSpan J (∑_{λ ∈ s} c λ)`.

## Proof of `mem_translateSpan_of_sum`

A function with unnormalized exponent `λ` is a generalized joint eigenvector of the
translations with character `a ↦ a^λ` (`mem_jointGenEigenspace_of_hasUnnormalizedExponent`), and
distinct parameters give distinct characters of `𝔄_{P_J}`
(`eisensteinPositiveParameters`). The translations commute, and `translateSpan J (∑ c λ)` is a
submodule invariant under all of them containing the sum, so
`GeneralizedEigenComponents.mem_of_sum_mem` gives the claim.
