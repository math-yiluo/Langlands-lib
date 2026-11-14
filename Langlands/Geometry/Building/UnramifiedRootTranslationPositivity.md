# Strict root positivity along descended apartment translations

Author: Worker 200.

For a field extension `K/k`, a lower split torus `S`, a torus map `f : S → T`,
and a supplied apartment class `D` for `T_K` in `G_K`, the definition
`KPApartmentData.descentTranslate` constructs the actual upper apartment point
with root-function family
`descentCocharacterMap k K f hS v +ᵥ x.val`.
The point belongs to the original apartment class by its translation
closure. The theorem `galois_fixed_descentTranslate` proves that it is fixed
by every coefficient automorphism when `x` is fixed.

Assuming `G` is smooth, `T_K` is split, and the upper root datum has opposite
factor pairs, the Prop-valued definition
`KPApartmentData.NonnegativeNearDescentTranslations` requires the actual
torus-then-field restricted value to stay nonnegative at
`descentTranslate x (t • v)` for all real parameters `t` sufficiently near
zero, for each `v`. The neighbourhood may depend on `v`.

The theorem
`KPApartmentData.strictPositive_iff_nonnegativeNearDescentTranslations`
identifies this condition with strict positivity at `x` for any nonzero
character of `S`. The corollary
`not_nonnegativeNearDescentTranslations_of_eq_zero` excludes it at value
zero. These assertions hold on all ambient rational points, including the
identity, and do not require root membership.

## Implemented proof and provenance

This is an internal specialization of the translation criterion in
`RootFunctionTranslationPositivity`. The published theorem
`galoisCocharacterAction_descentCocharacterMap` makes the added vector
coefficient-fixed; the root-function action law then proves preservation
of fixedness.

The equality `restricted_descentTranslate` is an application of the
published
`torusFieldRestricted_eq_vadd_of_eq_descent_vadd`. Rewriting by it identifies
the neighbourhood predicate with
`RootFunctionFamily.NonnegativeNearTranslations`. The equivalence and its
value-zero consequence follow from the elementary criterion in the imported
helper.

No root-valuation axiom on the restricted family, including V5, is used.
The hypotheses concern the original upper valuation. The field extension
need not be Galois: coefficient-fixed means invariance under every available
`k`-automorphism of `K`.

## Role and limits

For the maximal unramified extension this gives the neighbourhood criterion
at the exact translated upper points used in the fixed-point depth-zero
argument. When the starting point is fixed, all points tested by the
predicate are fixed.

The module does not construct an integral model or prove that its radical
preimage fixes a neighbourhood. That separate geometric assertion is needed
to apply this criterion to radical reduction and remains an obligation of
the depth-zero proof.
