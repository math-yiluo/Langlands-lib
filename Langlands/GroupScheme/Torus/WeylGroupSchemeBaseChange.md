# Base change of represented Weyl quotients

This internal helper transports the hypotheses of
`relativeWeylGroupQuotientPointsEquiv` to a field-valued base change. All group
schemes and bases lie in the same arbitrary universe.

Let `t : T ⟶ G` be a homomorphism from a commutative group scheme over `S`,
and let `b : S' ⟶ S` be any base morphism.
`torusNormalizer_isRepresentedBy_baseChange` states that if `n : N ⟶ G`
represents the actual all-test normalizer of `t`, then the pullback of `n`
represents the actual normalizer of the pullback of `t`. The proof combines
base change of a represented subgroup with the published base-change equalities
for the pointwise range and its normalizer.

Suppose a homomorphism `q : N ⟶ W` satisfies, for every test scheme `U` over
`S` and every point `y` of `N` on `U`,

`y ≫ q = 1 ↔ y ≫ n ∈ torusCentralizer t`.

`torusCentralizerKernel_baseChange` proves the same equivalence for the
pulled-back homomorphisms on every test scheme over `S'`. Applying the
multiplicative pullback point equivalence converts the left-hand equality to
the original equality. Compatibility with composition and the published
all-test centralizer base-change equality convert the right-hand membership
to the original membership. No flatness or geometric hypothesis is needed for
either transport result.

Now let `S' = Spec k` for an algebraically closed field `k`. Assume that `t`
is a monomorphism of schemes, that `N` and `W` are locally of finite type over
`S`, and that `q` is surjective on underlying scheme points. Each property is
preserved by base change, giving the corresponding field-fibre hypotheses.
`fibreRelativeWeylGroupQuotientPointsEquiv` applies the preceding transports
and `relativeWeylGroupQuotientPointsEquiv` to identify the rational relative
Weyl group of the pulled-back `t` with `W_b(k)`.
`natCard_fibreQuotientPoints_eq_relativeWeylGroup` records the resulting equality
of natural cardinalities.

The provenance is derived entirely from the imported Library interfaces.
The original quotient, its all-test kernel condition, and the stated geometric
hypotheses are inputs. This module neither constructs the quotient
nor proves finiteness or étaleness.
