# Rational consequences of reflected finite numerators

This internal prerequisite connects finite Laurent clearing to actual rational
continuations. It is a derived scalar assembly, with no new assertion attributed
to the original literature. It proves neither final dominant gamma/L target.

`HasReflectedFiniteNumerators q a aD A B M` is a proposition saying that some
finite Laurent polynomial `N` embeds as `A • a`, and its reflected polynomial
embeds as `(reflection (M⁻¹) * B) • aD`. Here `a` and `aD` are arbitrary bilateral
complex coefficient series, `A` and `B` are arbitrary Laurent polynomials, `M`
is a Laurent unit, and reflection substitutes `X ↦ q⁻¹ X⁻¹`. The definition
retains both clearing factors. It assumes no support, convergence, or model
realization property.

`laurentReflection_eq_reciprocal` identifies the dominant finite reflection with
the already defined Godement–Jacquet reciprocal Laurent map at inverse scalar.
Its proof expands the reciprocal unit's integer powers separately at nonnegative
and negative exponents, then uses Laurent monomial induction. Consequently
`laurentToRatFunc_reflection` reuses the published
`GodementJacquet.laurentToRatFunc_reciprocal` to identify its actual rational
image with `RationalReflection.subst q⁻¹`.

`clearedSpectralExpansion_laurentRationalIdentity` extends the existing
`clearedSpectralExpansion_rationalIdentity` from polynomial to finite Laurent
multipliers. For a natural residue parameter greater than one, assume the actual
convergent spectral expansion of `f` with coefficients `a`, a clearing identity
`ofLaurentPolynomial Q = A • a`, and rational continuation `R` of `f`.
The conclusion is `laurentToRatFunc Q = laurentToRatFunc A * R`. The proof
multiplies by a sufficiently large power of `T` to turn `A` into an ordinary
polynomial, applies the existing scalar theorem, and cancels that power only in
the rational-function field. It never cancels a polynomial acting on bilateral
series.

`reflectedNumerators_rationalIdentity` assumes the paired finite-numerator
proposition and, separately for each scalar family, an actual convergent spectral
expansion and rational continuation. It proves

```
subst qU⁻¹ (laurentToRatFunc B * RD) =
  laurentToRatFunc M * laurentToRatFunc A * R.
```

The expansion residue parameter `q > 1` and reflection scalar `qU : ℂˣ` are
independent in this generic theorem. Each expansion may hold on its own right
half-plane. Applying the preceding clearing theorem on each side, then using
rational substitution's involution and the inverse of the given unit proves the
formula. No common domain of original and reflected convergence is assumed.

`normalizedGenerator_divisibility_of_clearedExpansions` assumes that `P` is a
normalized generator for a set `S` of rational values and that a nonzero ordinary
polynomial `A` clears a convergent coefficient expansion of every member of `S`.
It proves `∃ Q e, X^e * A = Q * P`. The proof applies the published
`clearedSpectralExpansion_mem_reciprocalSpan` member by member, then
`reciprocalLaurentSpanClearing`. Thus the Laurent span has exactly the direction
needed for the denominator bound.

The prerequisites are the imported dominant Laurent reflection algebra,
bilateral spectral evaluation and rational-continuation uniqueness, reciprocal
substitution compatibility, and normalized-generator Laurent-span clearing.
Although the existing scalar clearing lemmas reside in
`AdjacentRankClearedContinuation`, these uses are its generic theorems before
the p-adic adjacent-rank specialization: no adjacent-rank base case is assumed.
Actual representation-theoretic convergence, first-block equations, parameter
continuation, and factor comparison remain separate obligations.
