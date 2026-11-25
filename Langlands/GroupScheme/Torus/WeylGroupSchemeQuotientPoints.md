# Algebraically closed points of a represented Weyl quotient

This is a derived helper for `WeylGroupSchemeFiniteEtaleStatement`. It identifies
the rational points of a supplied quotient with the Library's relative Weyl
group. It does not construct the quotient or assert its finiteness or étaleness.

For a monomorphism `t : T ⟶ G` over a field `k`, suppose `n : N ⟶ G` represents
the actual subgroup functor `torusNormalizer t`.
`normalizerRationalPointsEquiv` identifies `N(k)` with `normalizerPoints t`.
It composes the published represented-points equivalence with
`torusNormalizer_carrier_base`; the latter uses the monomorphism hypothesis to
recover a torus automorphism from the all-test normalizer condition.
The forward map is composition with `n`, and the inverse has the same
composition property.

Given any homomorphism `q : N ⟶ W`,
`normalizerQuotientRationalPointsHom` sends a normalizing point to its represented
lift followed by `q`. If the kernel of `q` on every test scheme is precisely the
inverse image of `torusCentralizer t` under `n`, its rational-points kernel is
`(centralizerPoints t).subgroupOf (normalizerPoints t)`. The proof evaluates the
supplied kernel condition on the identity test scheme, uses the inverse
composition property, and applies `torusCentralizer_carrier_base`.

Now assume `k` is algebraically closed, `N` and `W` are locally of finite type
over `k`, and `q` is surjective on underlying scheme points.
`rationalPoints.map_surjective_of_surjective` proves that `N(k) → W(k)` is
surjective. For each rational target point, scheme surjectivity puts its closed
point in the image. The published
`Lie.exists_rational_lift_of_mem_range` then supplies a rational section lifting
the entire target section. This argument needs neither smoothness nor
connectedness.

`relativeWeylGroupQuotientPointsEquiv` is the resulting multiplicative
equivalence

`relativeWeylGroup t = normalizerPoints t / centralizerPoints t ≃* W(k)`.

Its implementation identifies the denominator with the just-computed kernel and
uses the first isomorphism theorem for the surjective point homomorphism.
The formula on normalizing representatives is recorded by
`relativeWeylGroupQuotientPointsEquiv_mk`, and
`natCard_quotientPoints_eq_relativeWeylGroup` records the induced equality of
natural cardinalities, without a finiteness assumption.

The provenance is internal: all constructions follow from the imported
represented-subgroup and torus-normalizer interfaces, the published rational
lifting lemma, and Mathlib's quotient-group isomorphism theorem. No reductivity
or maximality hypothesis is used. The input kernel is an explicit hypothesis;
this module does not establish it for a newly constructed quotient.
