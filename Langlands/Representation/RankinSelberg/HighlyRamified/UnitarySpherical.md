# Spherical tests of unitary unramified principal series

Module `Langlands.Representation.RankinSelberg.HighlyRamified.UnitarySpherical`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It supplies the test
representations for the dual comparison of essential vectors in the p-adic case with trivial
L-factor. These are unramified principal series of `GL_(r+1)(F)` whose spherical Whittaker
functions are Jacquet's explicit functions `W(·; x; ψ̄)`. The field is a p-adic field `F` with
its canonical structures; `ϖ` is the canonical uniformizer `uniformizerUnit` and `q` the
residue cardinality.

## Provenance

The identification of spherical Whittaker functions with the Satake–Schur formula is
Shintani's formula, which the Library proves for unramified generic constituents
(`inverseSphericalTest_torus_schur`, module `RankinSelberg.SphericalWhittakerFormula`;
Jacquet–Shalika, Euler products II, §1.3). The irreducibility of a principal series of
norm-one unramified characters is the Library's `unitaryBlock_isIrreducible`. Genericity
comes from Zelevinsky's classification of generic representations (Zelevinsky 1980,
Theorem 9.7), proved in the Library as `Classification.genericSegmentProductExhaustion`.
The combination is internal to this project.

## Results

- `satakeSchur_add_const`: `s_(λ + t)(x) = (∏ x_i)^t s_λ(x)` for the Library's
  `satakeSchur`. The shifted weight `λ - λ_last` does not change, so this follows from the
  definition.
- `sphericalTest_eq_inverseSphericalWhittaker`. Let `σ` be an unramified generic constituent
  (`IsUnramifiedGenericConstituent F ψ σ χ`) and let `ψ` have conductor `O`. Let `σ` have
  central character `ω` with `ω(ϖ) = ∏ x_i`, where `x = characterValues F χ`. Then for every
  nonzero inverse-character functional `ℓ` of `σ`, the function of every normalized spherical
  test `w` is `inverseSphericalWhittaker hψ.1 ϖ q x`, the function `W(·; x; ψ̄)`.

  Proof. Both functions are left equivariant for the inverse standard character and right
  `GL_(r+1)(O)`-invariant. Both vanish at `ϖ^λ` for non-antitone `λ`: the test by
  `eval_torus_eq_zero_of_not_antitone`, and the explicit function by its definition. So both
  are the cell functions of their torus values (`eq_cellFunction`). It remains to compare the
  values at antitone `λ`. Write `λ = μ + t` with `t = λ_last`, so that `μ` is a partition
  exponent. The scalar `ϖ^t` is central (`torus_add_const`, `torus_const_eq_scalar`). The
  central character therefore gives `w(ϖ^λ) = (∏ x_i)^t w(ϖ^μ)`. Shintani's formula gives
  `w(ϖ^μ) = δ^(1/2)(ϖ^μ) s_μ(x)`. The explicit function has the same values: use
  `halfModulus_add_const` and `satakeSchur_add_const`.
- `unitaryBlock_isGeneric`: for `|w_k| = 1`, the Library's `unitaryBlock F w` is generic.
  It is the product of the singleton segments `[μ_(w_k)]` (`SegmentProductDatum.ofCuspidals`,
  isomorphism `ofCuspidalsInducedIso`). These segments are segment heads
  (`singletonSegment_isSegmentHead`) and pairwise unlinked, since their blocks are
  square-integrable (`squareIntegrableSegmentNonlinkage`). Then
  `genericSegmentProductExhaustion` applies.
- `unitaryBlockEquiv`: an equivalence from `unitaryBlock F z` to
  `principalSeriesOfTuple F z`. It is the induced equivalence
  (`normalizedProductInducedEquiv`) of the `ULift` equivalences of the one-dimensional
  factors.
- `principalSeriesOfTuple_isGeneric`: for `|z_k| = 1`, `principalSeriesOfTuple F z` is
  generic for every `ψ`. Transport `unitaryBlock_isGeneric` along `unitaryBlockEquiv`.
- `principalSeriesOfTuple_fixedVectors_ne_bot`: the principal series has a nonzero
  `GL_(r+1)(O)`-fixed vector (`normalizedProductInduced_fixedVectors_ne_bot`). Its
  one-dimensional factors are fixed by the kernel of the determinant norm, because the
  characters `χ_(z_i)` are unramified (`characterTuple_isUnramified`).
- `principalSeriesOfTuple_isUnramifiedGenericConstituent`: for `|z_k| = 1` the principal series
  is an unramified generic constituent of itself, with characters `characterTuple F z`. The
  subquotient is the whole representation with its inclusion
  (`subrepresentationSubtype`).
- `principalSeriesOfTuple_hasGLCentralCharacter`: the central character is `∏ χ_(z_i)`
  (`hasScalarCharacter_normalizedProductInduced`). A scalar `a` of `GL_1` has determinant
  `a`. `prod_characterTuple_uniformizer` computes its value `∏ z_i` at `ϖ`
  (`ord_uniformizer`).
- `principalSeriesOfTuple_nonempty_sphericalTest`: every nonzero inverse-character functional of
  a norm-one unramified principal series has a normalized spherical test. This is the
  Library's `unramifiedSphericalVector`, second clause.
- `principalSeriesOfTuple_sphericalTest_eq`: for `|z_k| = 1`, every such test is
  `W(·; z; ψ̄)`. Combine the results above with `characterValues_characterTuple`.
