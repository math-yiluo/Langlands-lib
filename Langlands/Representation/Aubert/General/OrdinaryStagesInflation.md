# Ordinary induction in stages and inflation

This internal construction supports the finite-length adapters for the actual
rational-point Aubert statements. It derives ordinary smooth induction in stages
for nested semidirect decompositions from the published ordinary stages and
split-quotient constructions. No new literature assertion is made.

Let `P₀ = M₀ ⋉ U₀` and `P₁ = M₁ ⋉ U₁` be semidirect decompositions in a
topological group `G`. Assume `P₀ ≤ P₁`, `M₀ ≤ M₁`, `U₁ ≤ U₀`, continuity of
the second Levi projection, and the literal restricted semidirect decomposition
of `P₀.subgroupOf M₁` into `M₀.subgroupOf M₁` and `U₀.subgroupOf M₁`.
For a smooth complex representation `A` of `M₀`,
`ordinaryStagesInflationEquiv` constructs a representation equivalence between:

- ordinary smooth induction from `P₀` of `A` inflated by its Levi projection;
- ordinary smooth induction from `P₁` of the inflation, by its Levi projection,
  of ordinary smooth induction inside `M₁` from `P₀.subgroupOf M₁` of `A`
  transported to `M₀.subgroupOf M₁` and inflated by the restricted projection.

The proof first uses `Induction.smoothStagesEquiv` for `P₀ ≤ P₁`. The inner
coefficient representation is trivial on the second Levi projection's kernel,
since that kernel is `U₁` and `U₁ ≤ U₀`. The published
`Induction.smoothSplitQuotientEquiv` therefore identifies the inner ordinary
induction with inflation of the inside-Levi induction. The two restricted
coefficient actions agree by
`IsSemidirectDecomposition.projection_subgroupOf`. Postcomposition by this
coefficient equivalence completes the construction. The representation
identification retains the actual right-translation actions and induced function
spaces. The coefficient and group universes are independent.

The module also provides `ordinaryInductionAsNormalizedEquiv` for a locally
compact nonarchimedean `G`, closed `U`, and a semidirect decomposition `P = M ⋉ U`.
If `IsUnimodularModulus U hU` holds, twisting `A` on `M` by the inverse of its
actual half-character cancels the normalization in `normalizedInductionFunctor`.
The equivalence is the pointwise identity after this cancellation. The proof
uses `closedHalfCharacter_eq_comp_projection`, followed by scalar cancellation.
The inverse character has the same open kernel, so it defines a smooth twist.
The corollary `isFiniteLength_ordinaryInduction` follows: if normalized
induction preserves finite length, ordinary induction of inflated smooth
finite-length Levi coefficients has finite length. Scalar twisting preserves
length by the published `finiteLength_twist_iff`, and a representation
equivalence transports finite length by a surjective group-algebra linear map.

This module does not identify a product of three Haar moduli, construct
normalized induction in stages, prove inside-Levi finite-length preservation,
or prove an Aubert identity. Its constructions are intended to support those
separate finite-length deductions.
