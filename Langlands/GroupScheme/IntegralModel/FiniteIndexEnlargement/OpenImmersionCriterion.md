# An affine open-immersion criterion from principal localizations

This module supplies a derived scheme-theoretic helper for the coordinate-ring
construction of finite-index enlargements. It introduces no new source
statement. Its inputs are Mathlib's principal-open topology and the published
Library theorem
`AbsoluteNoetherianApproximation.isIso_SpecMap_restrict_iSup_basicOpen`.

For commutative rings `B`, `A`, a ring map `φ : B →+* A`, and any indexed family
`s : ι → B`, `isOpenImmersion_specMap_of_away_bijective` proves that
`Spec A → Spec B` is an open immersion, assuming:

- the elements `φ (s i)` generate the unit ideal in `A`;
- each induced localization map `B[1 / s i] → A[1 / φ (s i)]`, represented by
  `Localization.awayMap φ (s i)`, is bijective.

No finiteness assumption on the index type, no injectivity assumption on the
original ring map, and no Noetherian hypothesis are required.

The proof takes the open `V = ⋃ i, D(s i)` in `Spec B`. The published
localization theorem makes the restriction of `Spec φ` over `V` an isomorphism.
The unit-ideal assumption says that its inverse image in `Spec A` is the whole
source, using `PrimeSpectrum.iSup_basicOpen_eq_top_iff`. Therefore `Spec φ`
factors as the inverse of the inclusion of that whole-source restriction,
the restriction isomorphism, and the open inclusion `V → Spec B`. The first
two maps are isomorphisms, so their composite with the last is an open
immersion.
