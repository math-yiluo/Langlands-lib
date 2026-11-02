# Full domain representations in actual relative Laurent annuli

This is an internal supporting construction for descent from relative Laurent
annuli. It lifts every full represented affinoid domain to the actual annulus
algebra and proves that the continuous Gauss section pulls its locus back to
the original locus. The proof derives these facts from the bounded pushout
property and naturality of the existing Gauss section. This explicit derivation
is its provenance; it does not claim a numbered external theorem.

## Actual lifted image

Let `K : Type u` be a complete ultrametric normed field, let `t > 0`, and let
`A` be an actual finite positive-polyradius presented affinoid algebra over `K`.
For `U : PresentedAffinoidAlgebra.Domain K A`, its data include an actual
presented algebra `B = U.algebra`, a bounded map `i = U.baseMap : A → B`, and
the closed locus `U.locus`. Its `Represents` property tests factorization
against every presented affinoid algebra over `K`, with arbitrary positive
polyradii.

Write `A_t` and `B_t` for the actual relative Laurent annulus quotients from
`RelativeLaurentGaussSection`. These append two inverse variables of radii
`(t,t⁻¹)` to the original presentations and retain their old relations. The
transport from `RelativeLaurentTransport` is the actual bounded map
`i_t : A_t → B_t`.

`restriction_comap_transport` proves that restricting a point pulled back
along `i_t` agrees with first restricting that point to `B` and pulling back
along `i`. Evaluation on each `a : A` reduces this assertion to the structural
formula `transport_baseMap`.

`liftedLocus K t U` is defined to be the actual range of the spectrum pullback
along `i_t`. `liftedLocus_subset_preimage` uses this commuting square and the
image-containment part of `U.represents` to show that every point in that
range restricts into `U.locus`.

## Pullback along the Gauss section

`preimage_gaussSection_liftedLocus` proves the exact equality

`gaussSection K A t ⁻¹' liftedLocus K t U = U.locus`.

For the forward inclusion, restriction sends every lifted-locus point into
`U.locus`, and restriction composed with the Gauss section is the identity.
For the reverse inclusion, the spectrum-image equality in `U.represents`
lifts a given point `x` of `U.locus` to a point `y` of `M(B)`. Naturality
`comap_transport_sectionPoint` then sends the Gauss point over `y` to the
Gauss point over `x`, giving a preimage in `M(B_t)`.

`image_restriction_liftedLocus` also proves that restriction maps the lifted
locus onto exactly `U.locus`. Containment is the earlier square argument;
the Gauss point over each point of `U.locus` supplies surjectivity.

## Full representation property

`represents_transport` proves that `i_t` represents `liftedLocus K t U`
against all presented affinoid tests over `K`. The locus is closed because it
is the continuous image of the compact spectrum of `B_t` in the Hausdorff
spectrum of `A_t`. Its image equality is its definition.

For a presented test algebra `R` and a bounded map `α : A_t → R` whose
spectrum image is in this locus, the containment proved above shows that
`α` restricted to `A` has image in `U.locus`. The original representation
property supplies a bounded map `β : B → R` with
`β.comp i = α.comp (baseMap K A t)`. The existing bounded annulus pushout
constructs `pushoutLift α β : B_t → R` and proves that its composition with
`i_t` is `α`.

To prove uniqueness, let another bounded map `θ : B_t → R` have the same
composition with `i_t`. The old structural square shows that the restriction
of `θ` to `B` and `β` agree after composition with `i`.
`U.represents.hom_ext` cancels `i` to identify these two maps.
`pushout_hom_ext` then identifies the maps on `B_t`, since their compositions
with both `i_t` and the structural map from `B` agree. This uses the original
full representation property without assuming a description of all spectrum
fibers.

`liftedDomain K t U` packages the actual algebra `B_t`, bounded map `i_t`,
actual-image locus and this proved `Represents` property as a
`Domain K A_t`. The three projection lemmas record its data. The final
`preimage_gaussSection_liftedDomain` states the same exact Gauss-section
pullback equality for the packaged domain.

## Scope

All parameters retain universe `u` and arbitrary positive real radii. The
construction allows trivial valuations, nonreduced and zero quotient algebras,
empty coordinate tuples and empty spectra. It assumes no strictness, radius
independence, rationality of the input domain, or pre-existing cover.

The lifted locus here is the actual image of `M(B_t)`. The proved equality
concerns its inverse image along the Gauss section; this unit does not assert
that it equals the full inverse image of `U.locus` along restriction. It does
not recast the annulus over an extension field or provide rational
decomposition or the host finite ambient rational covering theorem.
