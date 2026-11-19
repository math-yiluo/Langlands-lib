# Finite Whittaker products with a joint infinite residual

This is an internal algebraic and pointwise contribution to Task 7397. It
composes the actual finite Whittaker functional separation, transport from
embedded local coefficient models, and the paired partial-domain reduction.
It is derived from the imported Library and helper results. It does not claim
a separate direct translation of a literature theorem.

## Statement and scope

`FiniteWhittakerSemilocal.SemilocalProductStatement.{u,uQ}` quantifies over a
number field with compact adelic quotient, two actual cuspidal realizations of
`GL_(r+1)`, and their supplied spectral presentations. Each presentation's
embedded local components are irreducible and admissible. A finite set `S`
contains both exceptional sets. The character is a unitary adelic additive
character trivial on the number field; its canonical finite components at `S`
are supplied.

At each place of `S`, prescribe a nonzero standard Whittaker functional on the
first embedded local component and a nonzero inverse-character functional on
the second. Also prescribe arbitrary functions `f_v`, `f'_v` in their actual
coefficient models. They need not be nonzero. The statement constructs factor
vectors `a`, `a'` realizing exactly those functions, and factor vectors `a0`,
`a0'` normalized to have functional value one.

For all tensors `t`, `t'` in the respective dependent tensors of the actual
infinite-place source subspaces, form the actual global vectors through
`P.allPlaceTensorEquiv` and the finite pure tensors. If `X(a,t)` denotes this
construction, then for every point `g` of `unipotentIntegralOutside`,

```
W_psi(X(a,t))(g) * W_psi_inv(X'(a',t'))(g)
 = [W_psi(X(a0,t))(g_infty) * W_psi_inv(X'(a0',t'))(g_infty)]
   * product_{v in S} [f_v(g_v) * f'_v(g_v)].
```

Here `g_infty = infinitePoint S g` is the actual adelic point with the same
infinite components as `g` and every finite component equal to one. The scalar
in this identity is exactly one. The global residual pair uses the normalized
finite vectors; it is not asserted to coincide with the infinite restriction
of the original prescribed global vectors. In particular, no division by
`f_v(1)` or `f'_v(1)` is made.

The natural parameter `r=0` denotes `GL_1`. The finite set `S` may be empty.
The construction allows zero coefficient functions and zero infinite tensors.
Consequently the statement makes no nonvanishing claim. Its quantifiers retain
both field and presentation universe parameters.

## Implemented proof

`infinitePoint` and `localFinite` use the actual multiplicative adelic and
finite-place splitting equivalences. Projection lemmas show that the former
has finite components one and the latter has the original components at `S`
and identity elsewhere. `retainedPoint_eq` proves that their product is the
retained point from `FiniteWhittakerPartialDomain`: apply the adelic group
equivalence and compare its infinite and finite components.

`inverseFinite` specializes the already published `inverseCharacter` to the
canonical topology on the p-adic completion. `canonical_inverse` proves that
inverting a supplied canonical finite character gives the canonical component
of the inverse global character. It takes inverses of the given pointwise
canonical-component equality. The global inverse character and its
complex-valued identity are reused from
`EqualDualEulerFactorizationReduction`.

`coefficient_eq_product_at_retained` applies the actual finite translated
coefficient formula at `infinitePoint`, translating by `localFinite`. The base
point is identity at `S`, and the translating element is integral away from
`S` because its components there are one. The projection lemmas identify the
local factors with the original `g_v`. This proves the single-function product
at the retained point, with the normalized finite reference vector in the
residual coefficient.

`pair_eq_product` first uses `whittaker_pair_eq_retained` on the entire partial
domain. That imported result uses invariance under combined integral
translations away from `S` and cancellation of opposite left-unipotent
characters. Apply the single-function formula to each member, using the
inverse global and finite characters for the second member. Distribute the
finite products and commute complex factors. The resulting scalar is one;
no measure comparison occurs in this step.

`exists_prescribed_pair` chooses the factor vectors through
`FiniteWhittakerModel.factorVectorData`. This uses the genuine representation
equivalence between the supplied tensor factor and the embedded local
component, so each prescribed coefficient function is realized exactly.
Pulling a nonzero functional through this equivalence remains nonzero. For
each pulled functional choose a vector of value one by scaling a vector on
which it is nonzero. Applying `pair_eq_product` and substituting the exact
coefficient equalities proves the displayed formula. The final theorem
`finiteWhittakerSemilocalProduct` introduces the statement's binders and applies
this construction.

## Remaining global obligations

The infinite variables remain together in one actual global residual pair.
The module proves no factorization of that pair into individual real or
complex Whittaker functions, no arbitrary infinite-group tensor covariance,
no required archimedean restriction identities, and no archimedean integral
nonvanishing. It does not yet prove the dual-point product or compare ordinary
and dual normalization constants. Local functional nonzeroness is an explicit
input, although the imported local theory supplies such data in applications.
The construction is pointwise and asserts no integral identity or convergence.

The full `ArchimedeanFactorizationStatement` and either unconditional
archimedean factorization conjunct remain open. This result assumes no
algebraic archimedean Whittaker uniqueness and no factorization hypothesis for
the global Whittaker functions.
