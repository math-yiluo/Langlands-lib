# Stabilized Jacquet functionals on Shahidi induction

This module restricts the published scalar Jacquet integrals to the actual
induced representations `I(s, π₁ ⊗ π₂)` and `I(-s, π₂ ⊗ π₁)`. It constructs
linear functionals on their stabilization domains and constructs a total
functional only from a proof that the domain is the whole induced space.
It does not prove stabilization of every section or existence of the local
coefficient.

## Source and provenance

The original is Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)* (1984), registered as `shahidi-1984-fourier`,
SHA256 `a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Printed page 72, equation (0.2) and the display following (0.3), defines the two
functionals. Printed page 78, equation (1.1) and the paragraph following it,
explains their interpretation by sufficiently large compact open truncations,
after right translation by the inverse Weyl element. Both pages were reread
visually for this unit.

This is a derived restriction construction. It uses `JacquetIntegral` for the
integrands and stable scalar integrals, `Induction` for the actual carriers
and evaluation maps, and the published `pairFunctional` in
`LocalCoefficientPadic` for the tensor of the two linear forms. Despite its
module name, the latter tensor-functional construction is algebraic over
arbitrary complex vector spaces. No new analytic theorem is used in defining
or proving this restriction.

The induction convention and the documented twice-halved printed exponent
issue are inherited from `Induction`: normalized induction twists the factors
by `|det|^(s/2)` and `|det|^(-s/2)`, producing covariance exponents
`(s+n+1)/2` and `-(s+m+1)/2` for the ranks used here. This unit does not alter
that documented interpretation of the source.

## Two actual realizations

All ranks are positive: the two factor ranks are `m+1` and `n+1`.
The field universe and the common universe of the two representation carriers
are independent. The carriers are arbitrary algebraic complex modules, with
no norm or topology imposed on them.

In namespace `Langlands.Shahidi`, the construction uses the actual
`SourceSpace abv hopen` and `TargetSpace abv hopen` over a field with continuous
ring operations, a measurable structure, and a real absolute value whose
norm-one units form an open set. The source and target evaluations are
`sourceEval` and `targetEval`.

In namespace `Langlands.PadicField.TopologicalData`, it uses the actual
`T.ShahidiSourceSpace` and `T.ShahidiTargetSpace`, with evaluations
`T.shahidiSourceEval` and `T.shahidiTargetEval`. The topology and continuous
ring operations are obtained from the supplied p-adic topological data.
These are the same carriers used by the published p-adic intertwining
operator and local-coefficient relation, not newly defined models.

The supplied character `ψ` is unitary and continuous. The forms `ℓ₁` and `ℓ₂`
are arbitrary complex-linear forms at this definition stage. The scalar form
on the source carrier is `pairFunctional ℓ₁ ℓ₂`, and that on the target is
`pairFunctional ℓ₂ ℓ₁`. On pure tensors these evaluate as the respective
products. The source integral uses exchanged-radical coordinates of size
`(n+1) × (m+1)`, the block Weyl matrix, and the conjugate standard character.
The target uses original-radical coordinates of size `(m+1) × (n+1)` and the
inverse block Weyl matrix. These formulas are precisely the distinct
published `HasJacquetIntegral` and `HasSwappedJacquetIntegral` relations.

## Graphs, domains and functionals

Each namespace has `IsSourceJacquetFunctional` and
`IsTargetJacquetFunctional`. These are Prop-valued graphs for a supplied
linear form `Λ` on the whole induced carrier. The assertion is that every
section has the specified stable integral with value `Λ f`. The graphs do
not assert existence of `Λ`. Their `.unique` lemmas show that two forms with
the same graph are equal, pointwise by uniqueness of the stable scalar
integral.

For the domain and partial functional constructions, `h` is a proof that the
appropriate rectangular coordinate space contains one compact open additive
subgroup. This supplies the zero element of the stabilization submodule;
it says nothing about stabilization of nonzero sections.

The general namespace provides:

- `sourceJacquetStableDomain` and `targetJacquetStableDomain`;
- `sourceJacquetStableFunctional` and `targetJacquetStableFunctional`;
- `sourceJacquetFunctional` and `targetJacquetFunctional`.

The p-adic namespace provides the corresponding names with prefixes
`shahidiSourceJacquet` and `shahidiTargetJacquet`.

Each stable domain is the preimage of the published Jacquet stabilization
submodule under the actual induced evaluation linear map. The `mem_` lemmas
identify membership with existence of a stabilized scalar. The stable
functional composes that evaluation map, restricted to the domain, with the
published linear stabilized functional. Its `_spec` theorem proves that its
value satisfies the defining stable integral relation.

The last pair of constructors takes an explicit proof `hall` that its stable
domain equals the top submodule. It embeds every induced section into the
domain using that proof, then applies the partial functional. The resulting
`_spec` theorem proves the whole-space graph. There is no unconditional
selection of an integral value for a section outside the domain.

In each namespace, `exists_isSourceJacquetFunctional_iff` and
`exists_isTargetJacquetFunctional_iff` prove that existence of a total linear
functional with the graph is equivalent to the stable domain being the whole
space. The forward implication uses the graph value as a stabilization
witness for each section; the reverse uses the conditional constructor.
Thus linearity and uniqueness add no further analytic hypothesis once
stabilization for every section is proved.

## Scope

No Haar condition or Borel compatibility is required for these restriction
constructions. Applications to Shahidi's analytic assertions must impose
those conditions, nonzero Whittaker forms, genericity and the local-field
hypotheses separately. In particular the graph does not include Whittaker
equivariance, nonvanishing, multiplicity one, or any theorem about rational
continuation. No independence from the chosen measures is asserted. The
choice of compact-open existence witness does not change the specified
value: any two total forms with the same graph are equal by `.unique`.

Stabilization means integrability on every sufficiently large compact open
additive subgroup and equality of all such truncated integrals. It never
asserts absolute integrability on the full noncompact radical. The analytic
stabilization, Whittaker and local-coefficient existence statements are
separate obligations following this definition unit.
