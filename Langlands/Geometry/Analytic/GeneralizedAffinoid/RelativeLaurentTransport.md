# Bounded transport of the actual relative Laurent annulus

This is an internal construction extending `RelativeLaurentGaussSection` and
`RelativeLaurentGaussContinuity`. It constructs the actual bounded annulus map
induced by a bounded coefficient algebra map, proves functoriality and a norm
bound, and proves naturality of the continuous Gauss section. Its provenance is
the explicit composition and comparison of the existing constructions described
below; it does not claim a numbered external result.

## Parameters and actual quotients

Let `K : Type u` be an ultrametric normed field, let `t` be a positive real
number, and let `A`, `B`, and `C` be actual presented affinoid algebras over `K`.
Write `A_t` for `RelativeLaurentAnnulus.algebra K A t`: the enlarged scalar
weighted Tate presentation obtained by adjoining two variables of radii
`(t,t⁻¹)` and imposing their product equal to one, together with the original
relations of `A`. All relation ideals in this construction are closed generated
ideals. The structural map is `baseMap K A t`.

The extensionality lemma `hom_ext` does not require completeness of `K`. Two
bounded maps from `A_t` into any normed commutative `K`-algebra agree if they agree
on the image of `A` and the two new coordinates. Its proof applies
extensionality of maps from the enlarged scalar series algebra to all its
coordinates, and then uses surjectivity of the presentation map. The target can
lie in a separate universe `v`.

The remaining transport construction assumes `CompleteSpace K`. For any
`φ : BoundedAlgHom K A B`, `seriesTransport` is the composition

1. from the enlarged scalar series over `K` to the relative series over `A`,
   using `Adjoin.relativeSeriesEvaluation`;
2. coefficientwise application of `φ`, using `mapCoefficientsAlgHom`;
3. evaluation of the relative series over `B` in `B_t`, using
   `Adjoin.relativeEquationInverseEvaluation`.

The append-left formula evaluates the old variables through `φ` and the actual
structural map of `B_t`; the new-variable formula gives the corresponding new
coordinate of `B_t`. The old ideal therefore vanishes, and the inverse relation
vanishes because the target coordinates have product one.
`transport` descends this series map to a bounded `K`-algebra map `A_t → B_t`.

## Structural formulas and bounds

`transport_baseMap` states
`transport φ (baseMap a) = baseMap (φ a)`, and
`transport_newCoordinate` preserves each of the two new coordinates. The
corresponding equality of composed structural maps is
`transport_comp_baseMap`. Extensionality on these generators proves
`transport_id` and `transport_comp`.

For every positive real constant `c`, if `‖φ a‖ ≤ c * ‖a‖` for every `a`, then
`norm_transport_le` proves
`‖transport φ b‖ ≤ c * ‖b‖` for every `b : A_t`. Both relative evaluations are
contractive, coefficient transport preserves the stated constant, and closed
quotient descent preserves it. No contractivity hypothesis on `φ` is needed.

`transport_coordinateUnit` preserves the actual unit defined by the two inverse
coordinates. Applying the unit map to integer powers gives
`transport_coordinateUnit_zpow`. Induction on finite Laurent expressions then
proves `transport_polynomialMap`: evaluating a finite Laurent polynomial in
`A_t` and transporting it equals evaluating the polynomial obtained by applying
`φ` to every coefficient in `B_t`.

## Naturality of the Gauss section

For `y : BanachSpectrum B`, let `x` be its pullback along `φ`. The completed
residue fields at `x` and `y` can be different. No identification or chosen map
between them is used. The coefficient of a finite Laurent polynomial `p` has
norm `x(p_n)` at `x`, whereas the transported coefficient at `y` has norm
`y(φ(p_n))`; these are equal by the definition of spectrum pullback.

`norm_residuePolynomial_transport` uses these coefficient norm equalities and
the coefficientwise characterization of the Gauss norm bound to prove equality
of the two residue Laurent norms. This lemma does not require completeness of
`K`. `sectionPoint_polynomialMap_norm` identifies Gauss section evaluation of a
finite expression with its residue Laurent norm, using the existing evaluation
formula and the isometric inclusion into the Laurent completion.

Consequently `sectionPoint_transport_polynomialMap` proves naturality on all
finite Laurent expressions. Such expressions have dense image in `A_t`. Both
seminorms are continuous as functions of the algebra element, by joint spectrum
evaluation continuity and boundedness of transport. The dense-range equalizer
lemma extends their equality to every element of `A_t`, giving
`comap_transport_sectionPoint`:

`comap (transport φ) (sectionPoint y) = sectionPoint (comap φ y)`.

Finally `comap_transport_comp_gaussSection` states the same identity as an
equality of continuous maps from `BanachSpectrum B` to `BanachSpectrum A_t`.

## Scope

All parameters retain the full universe `u`, arbitrary positive real radius,
and trivial valuations. No strictness, radius independence, reducedness or
nonzero hypothesis is imposed. Empty spectra and zero quotient algebras are
allowed by the universally quantified maps and identities.

This supporting unit constructs transport and its Gauss-section compatibility.
It does not establish scalar extension of represented domains, strictification,
rational pullback decomposition, or the host finite ambient rational covering
proposition.
