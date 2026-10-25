# Removing a target-Levi factor from a representative

This is a derived construction for changing an already supplied ambient
representative. It uses actual product Levis, their topology from a p-adic field,
and the published conventions for inverse pullback, positive real determinant
twisting, and normalized induction. The source and target block shapes may differ;
the field and the two representation carriers have independent universes. There
is no positive-rank, multiple-block, irreducibility, or chamber assumption.

## Coordinate adjustment

Let `A` and `B` be block shapes of the same ambient rank, let
`e : A.Levi F.Carrier ≃ₜ* B.Levi F.Carrier`, and let `m` belong to the target
Levi. The definition `T.removeTargetLeviFactor e m` is the continuous
multiplicative equivalence

```text
e'(x) = m⁻¹ * e(x) * m.
```

It is the composite of `e` with `T.innerLeviEquiv B m⁻¹`. Its displayed
application formula follows by simplifying the definition and the double inverse.

For a concrete conjugate block pair `P`, suppose the old coordinates implement
an ambient representative `z`, and a factorization is supplied:

```text
B.leviEmbedding F.Carrier (e x) = z * P.leviEmbedding x * z⁻¹,
z = B.leviEmbedding F.Carrier m * y.
```

`removeTargetLeviFactor_embedding` proves that `e'` implements the exact
representative `y`. The proof expands the homomorphism on `m⁻¹ * e(x) * m`,
substitutes the two hypotheses, and cancels the embedded Levi factors.

## Characters and representations

`removeTargetLeviFactor_character` preserves any established identity between
the source real determinant character pulled back along `e⁻¹` and the target
real determinant character. The inverse of `e'` is `e⁻¹ ∘ conj(m)`, so the new
pullback is the old one followed by inverse-inner pullback for `m⁻¹`. The
previous character identity and
`leviRealPowerCharacter_comp_innerLeviEquiv` give the result. Both real vectors
are unrestricted, including their central direction.

For any source representation `σ`, `removeTargetLeviFactorPullbackEquiv`
constructs an equivalence from the pullback along `(e')⁻¹` to the pullback
along `e⁻¹`. It applies `innerPullbackEquiv` to the latter representation and
the target Levi element `m⁻¹`. Its underlying linear map is the old pullback's
action at `m⁻¹`. Thus no representation isomorphism is assumed for this step.

`removeTargetLeviFactorRepresentationEquiv` composes that equivalence with a
supplied equivalence from the old pullback to any target representation `τ`.
This preserves an established untwisted representation identity, with the
carriers of `σ` and `τ` in independent universes.

`removeTargetLeviFactor_tempered_iff` uses that same explicit equivalence and
`isLeviTempered_iff_of_equiv`. Both sides use the actual target Levi central
quotient and quantify over its Borel Haar measures through
`RelativeRegularComparison.IsLeviTempered`.

`removeTargetLeviFactorInducedEquiv` gives an equivalence between the actual
normalized inductions of the two pullbacks after the same target real twist.
It specializes `innerLeviInducedEquiv` to `m⁻¹` and the old pullback. The
imported construction twists the inner intertwiner and then postcomposes
induced functions with it. Right translation and positive half-modulus
covariance retain their existing definitions.

## Actual subgroup identities

The private group lemma `map_conj_remove_left` proves the following elementary
fact. If conjugation by `d*y` maps a subgroup `H` to `K`, and conjugation by
`d⁻¹` preserves `K`, then conjugation by `y` maps `H` to `K`. It composes
subgroup images and proves `conj(d⁻¹) ∘ conj(d*y) = conj(y)` pointwise by group
cancellation.

The three exported specializations remove `B.leviEmbedding F.Carrier m` from
the representative in established identities for the actual parabolic, split
component, and embedded Levi:

* `parabolic_map_conj_removeLeviFactor` uses membership of the embedded Levi
  element and its inverse in the target parabolic, whose elements normalize it.
* `splitComponent_map_conj_removeLeviFactor` applies
  `splitComponent_map_conj_of_standardizer` to the standard target pair and
  `m⁻¹`. The block-scalar subgroup is centralized by every target Levi element.
* `leviSubgroup_map_conj_removeLeviFactor` uses membership of the embedded
  element and its inverse in the target Levi subgroup.

## Diagonal-times-permutation specialization

Suppose `z = D(a) * permutation n F.Carrier w`, where `D(a)` is the singleton
block-scalar matrix of a tuple of coordinate units. Set
`m = B.diagonalLevi F.Carrier a`. The identity
`B.leviEmbedding_diagonalLevi` identifies its embedding with `D(a)`.
`removeDiagonalFactor_embedding` then proves the exact coordinate embedding
formula for that permutation matrix. All character, representation, induction,
temperedness, and subgroup results above apply to the same `m`; permutation
membership in the actual diagonal-torus normalizer is independently supplied
by `permutation_mem_singletonSplitComponent_normalizer` in `DiagonalLevi`.

## Provenance and scope

All results are elementary consequences of `InnerLeviTransport`,
`PairConjugation`, and `DiagonalLevi`, with subgroup-image composition from
Mathlib. No external theorem is cited or assumed. The factorization and the
old coordinate and subgroup identities are explicit inputs where used.

This module removes the diagonal factor once a diagonal-times-permutation
factorization is supplied. It does not assert that an arbitrary normalizer
element admits such a factorization, construct a semistandard standardizer,
recover inducing data from equivalent quotients, or prove
`GLSemistandardLanglandsConjugacyStatement`. Those remain separate obligations.
