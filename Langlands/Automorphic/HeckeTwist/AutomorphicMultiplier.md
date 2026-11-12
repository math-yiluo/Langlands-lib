# Determinant multiplication by any Hecke character on automorphic forms

Author: Worker 5136.

This internal module shows that multiplication by `χ ∘ det`, for an arbitrary
Hecke character `χ` of a number field `F` (no finite-order hypothesis), maps
the automorphic forms on `GL_n(𝔸_F)` (the Library's
`automorphicSubrepresentation F n`) onto themselves, and records how the
resulting automorphism interacts with the finite right action and the
differential operators.

## Polynomial growth

`hasPolynomialGrowth_heckeDeterminantMultiplier`: if a continuous
`GL_n(F)`-invariant function `f` has polynomial growth (the Library's
`HasPolynomialGrowth F n`, a bound on every infinite slice `a ↦ f(pair a b)`),
then so does `determinantMultiplier n χ f`. On the slice of `b`, the value at
`pair a b` factors as `χ(det (ofFinite b)) · χ(det (ofInfinite a)) · f(pair a b)`
(`HeckeCharacter.adelicDeterminant_pair_val`, module `SmoothMultiplier`). The
archimedean factor has polynomial growth by
`HeckeCharacter.hasPolynomialGrowth_adelicDeterminant_ofInfinite` (module
`Global.ArchimedeanCharacterGrowth`), products of functions of polynomial
growth have polynomial growth (`ArchimedeanGL.HasPolynomialGrowth.mul`), and
the finite factor is a constant on the slice.

## Automorphic forms

- `mem_automorphic_heckeDeterminantMultiplier`: the smooth multiplier
  `FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ` (module
  `SmoothMultiplier`) maps automorphic forms to automorphic forms. The three
  conditions are center-finiteness
  (`isCenterFinite_heckeDeterminantMultiplier`, module
  `DifferentialMultiplier`), `K_∞`-finiteness (the Library's
  `isInfiniteFinite_determinantMultiplier`, valid for every Hecke character)
  and polynomial growth (above).
- `AutomorphicForms.heckeDeterminantMultiplier n χ`: the resulting continuous
  linear automorphism of `AutomorphicForms F n`. Surjectivity onto the
  automorphic forms uses the multiplier of `χ⁻¹` and the Library's
  `determinantMul_inv_apply`.
- `heckeDeterminantMultiplier_val`, `toContinuous_heckeDeterminantMultiplier`,
  `evaluate_heckeDeterminantMultiplier`,
  `evaluate_heckeDeterminantMultiplier_symm`: the automorphism and its inverse
  multiply values pointwise by `χ(det g)` and `χ(det g)⁻¹`.
- `finiteRightAction_heckeDeterminantMultiplier`: right translation by a
  finite adelic element `d` of a multiplied form equals
  `χ(det (ofFinite d))` times the multiplier applied to the translated form.
- `envelopingAction_heckeDeterminantMultiplier`: for every element `a` of the
  universal enveloping algebra,
  `D(a) (χ·f) = χ · D(heckeEnvelopingShift n χ a) f`, where
  `heckeEnvelopingShift n χ` is the shift automorphism of module
  `DifferentialMultiplier`, built from the derivative of the archimedean
  determinant factor of `χ`.

Provenance: internal. This generalizes the automorphic-forms part of the
Library module `Langlands.Automorphic.AutomorphicDeterminantMultiplier` from
finite-order characters to all Hecke characters. It is an ingredient for
Henniart (2000), §2.2, which twists by arbitrary quasicharacters; no
correspondence with a particular passage of the literature is claimed.
