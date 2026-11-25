# Detection in noetherian rings by local Artinian quotients

This internal algebraic construction supports the Artinian-test
step in the proof of the fibrewise central-isogeny criterion. Its proof uses
Mathlib's Krull intersection theorem and detection of zero by maximal
localizations. It requires no approximation theorem.

For a commutative local ring `A`, `LocalTestRing A n` is the actual quotient
`A/m^(n+1)`, where `m` is its maximal ideal. These quotients are nontrivial
and local. If `A` is noetherian they are Artinian: the maximal ideal in the
quotient is the image of `m`, and its `(n+1)`-st power is zero.

`local_eq_zero` proves that an element of a noetherian local ring is zero
if its images in every positive maximal-ideal quotient vanish. Quotient
vanishing puts the element in every positive power of the maximal ideal;
it belongs to the zeroth power as well. Krull intersection makes this
intersection zero.

For any commutative ring `R`, `evaluation R` is the ring homomorphism to
the product indexed by all maximal ideals `P` of `R` and natural numbers
`n`, with factors `(R_P)/(m_P)^(n+1)`. Its component is the composite of
the localization map and the actual quotient map. `evaluation_apply`
records this component formula.

If `R` is noetherian, `evaluation_injective` proves that this map is
injective. A kernel element vanishes in every quotient of each maximal
localization, hence in that localization by `local_eq_zero`, and then in
`R` by detection of zero at maximal localizations. The construction also
covers the zero ring, where there are no maximal ideals and injectivity
has the same proof. `ringHom_ext` applies this injectivity to equality of
ring homomorphisms with any commutative source ring, allowing a different
universe for that source.

This is a ring-level detector. It does not assert equality of arbitrary
scheme morphisms, centrality of any group scheme, or detection on
Artinian tests for an arbitrary nonnoetherian ring. Those require
additional arguments.
