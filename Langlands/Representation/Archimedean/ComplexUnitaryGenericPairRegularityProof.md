# Proof: Getz–Hahn, Theorem 11.5.2, complex case

`complexUnitaryGenericPairRegularity` proves
`Langlands.Archimedean.ComplexUnitaryGenericPairRegularityStatement` at universes `uV` and
`uW`. Take two irreducible admissible generic unitarizable modules: a
`(𝔤𝔩_n(ℂ), U(n))`-module on `V : Type uV` with standard parameter `ds`, and a
`(𝔤𝔩_m(ℂ), U(m))`-module on `W : Type uW` with standard parameter `ds'`. Then the denominator
of `complexPairLFactor ds ds'` does not vanish at any `s` with `1 ≤ Re(s)`.

## Proof as implemented

The proof is a single term that combines three published Library theorems.

1. `complexUnitaryGenericPairRegularityReduction.{uV, uW}` proves
   `ComplexUnitaryGenericPairRegularityReductionStatement`. This statement says that the
   exponent bound at universe `uV`, the exponent bound at universe `uW` and the right
   half-plane regularity of complex pair `L`-factors together imply the target.
2. `complexUnitaryGenericExponentBound` proves `ComplexUnitaryGenericExponentBoundStatement`,
   which bounds every exponent of a unitary generic module by `|Re t| < 1/2`. Its universe is
   a parameter, so it is instantiated once at `uV` and once at `uW`.
3. `complexPairLFactorRightHalfPlaneRegularity` proves
   `ComplexPairLFactorRightHalfPlaneRegularityStatement`. It says that the denominator does
   not vanish when `Re(s) + Re(t) + Re(t') > 0` for all exponents `t` of `ds` and `t'` of
   `ds'`.

Applying the reduction to these three proofs gives the statement. The reduction itself does
the arithmetic: each exponent has real part greater than `−1/2`, so
`Re(s) + Re(t) + Re(t') > 1 − 1/2 − 1/2 = 0` when `Re(s) ≥ 1`.

## Provenance

J. R. Getz and H. Hahn (2024), *An introduction to automorphic representations*
(`getz-hahn-2024-automorphic-representations`), §11.5, p. 304 (PDF page 315), sets up the
irreducible admissible generic pair. Theorem 11.5.2 on p. 305 (PDF page 316) states that for
unitary representations the pair `L`-factor is holomorphic and nonzero on `Re(s) ≥ 1`.
The Library's `F = ℂ` statement expresses this as nonvanishing of the entire denominator
of its reciprocal-entire pair factor. It takes the two standard parameters as hypotheses;
this proof does not construct them. Getz–Hahn refer to Barthel–Ramakrishnan (1994), §2, for
the archimedean case; that proof is not used here.

The route is the one recorded in step 4 of "Why the statements are true" in the Markdown of
`UnitaryGenericPairRegularityStatement`: the exponent bound followed by the elementary
regularity of the `Γ`-factors. The provenance of the exponent bound for `GL_n(ℂ)` is
described in the Markdown of its proof module, `ComplexUnitaryGenericExponentBoundProof`.
