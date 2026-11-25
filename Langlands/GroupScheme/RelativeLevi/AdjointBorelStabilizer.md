# Actual adjoint-action Borel stabilizers over a ring

This is an internal construction from the Library's actual
proper parabolic quotient, morphism descent along fppf surjections,
self-normalization, and transfer of a represented subgroup functor to a group
scheme. It supplies the actual stabilizer subgroup needed for Borel reduction
in the semilocal inner-form problem.

For a commutative ring `R`, a reductive group scheme `G` over `Spec R`, a relative
Borel `i : B ⟶ G`, an fppf quotient `q : G ⟶ A` with full scheme-theoretic kernel
`center G`, and an automorphic action `a` of `A` on `G` whose restriction through
`q` is conjugation, `IsRelativeBorelSubgroup.adjointStabilizerData` constructs:

- An actual group scheme `P` and homomorphisms `j : P ⟶ A` and `qB : B ⟶ P`.
- A monomorphism `j` whose all-test range is exactly
  `a.subgroupStabilizer (SubgroupFunctor.range i)`.
- The identity `i ≫ q = qB ≫ j` and a cartesian square of schemes over `Spec R`.
- Flatness, surjectivity, and local finite presentation of `qB`, and closedness
  of the immersion `j`.

Here stabilizing a subgroup means preserving membership on every relative
test scheme and after every further restriction. The range certificate uses
this full subgroup functor. The input quotient predicate requires flatness,
surjectivity, local finite presentation, and equality of the actual kernel
range with the center; no quotient of `B` is supplied as an input.

The implementation first proves `SubgroupFunctor.center_le_normalizer`:
central points centralize every subgroup on all refinements and hence normalize
it. Relative Borel self-normalization then gives
`IsRelativeBorelSubgroup.center_le`, including the full center without any
smoothness or reducedness assumption on that center.

The construction uses the published `RelativeParabolicQuotient.existence` to
obtain the proper scheme `Q = G/B` and the exact right-coset fibre condition on
every test scheme. Because the full kernel of `q` lies in `B`,
`HomogeneousQuotientFactorization.desc` descends the map `G ⟶ Q` to a map
`r : A ⟶ Q`. This descent uses the effective epimorphism property of an fppf
surjection.

The generic lemma `SubgroupFunctor.mem_iff_descendedCoset_eq` identifies any
fppf-local subgroup `F` of `A` with full inverse image `range i` under `q` as
the identity fibre of `r`. It pulls a test point back along `q`, checks the
identity-coset condition using the exact fibres of `G ⟶ Q`, and descends
membership and equality along that fppf cover. In the Borel application,
the action restriction identifies the inverse-image stabilizer with the
normalizer of `B`, which equals `B`.

`SubgroupFunctor.quotientSubgroupDataOfCosetMap` represents that fibre by the
equalizer of `r` and the constant identity-coset map. A separated `Q` makes
the equalizer inclusion a closed immersion. The published
`representingGroupScheme` and `representingHom` transfer the subgroup laws
to this represented scheme and provide the exact range certificate. Factoring
`B ⟶ G ⟶ A` through it gives `qB`. The generic
`isPullback_of_comap_range` proves the square cartesian using the exact full
inverse image on every test. Base change of `q` then proves that `qB` is fppf.
In the application, properness of `Q` supplies separatedness.

The record `SubgroupFunctor.QuotientSubgroupData` retains these maps,
certificates, square, and morphism properties. Its theorem `kernel_eq` gives
the exact equality
`range (kernelι qB) = (range (kernelι q)).comap i`
using the commuting square and monicity of `j`. Thus, under the specified
ambient kernel equality, the new projection has kernel
`(center G).comap i`; this is the quotient of `B` by its included ambient
center in the fppf sense.

All generic lemmas work over an arbitrary base scheme when their displayed
coset-map, locality, separatedness, and morphism hypotheses are supplied.
The Borel existence construction works over any commutative ring and requires
no semilocality or reductivity hypothesis on `A`. It does not construct the
ambient adjoint quotient or its action, a unipotent filtration, a torus
presentation, a vanishing theorem, or a proof of the semilocal inner-form
statement.
