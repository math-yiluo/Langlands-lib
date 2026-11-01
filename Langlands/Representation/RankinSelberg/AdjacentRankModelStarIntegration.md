# Integrating the adjacent-rank unipotent orbit comparison

This internal helper derives ambient integral equalities from equalities of
unipotent orbit averages. It uses the existing `generalLinearHaar F n` and
`unipotentHaar F n` on GL_(n+1) and its actual upper-unipotent subgroup, for every
nonarchimedean local field and every natural `n`, including zero. No Fourier
identity or representation-theoretic assertion is assumed or established here.

`adjacentRank_integral_eq_of_left_unipotent_averages` applies the published complex
Weil formula for `unipotentQuotientHaar` to two continuous compactly supported
complex functions. Quotient induction transfers the supplied orbit equality to
the quotient, and multiplication by the supplied complex constant commutes with
integration. The quotient measurable space is chosen to be its Borel space
inside the proof, so there is no quotient-measure premise in the theorem.

`adjacentRank_integral_eq_of_right_unipotent_averages` applies that result to
`f(h⁻¹)` and `q(h⁻¹)`. Inversion reverses the order of multiplication and
preserves both normalized Haar measures. The GL inversion invariance is imported
from `generalLinearHaarSymmetries`; the unipotent inversion invariance is the
published `unipotentHaar_isInvInvariant`. Inversion is a homeomorphism, so both
pulled-back functions remain continuous and compactly supported.

Write `iota` for inverse transpose and `w` for the unsigned long Weyl element.
`adjacentRankRightWeylInverseTranspose` packages `h ↦ iota(h) * w` as an actual
homeomorphism of the positive-rank GL group. Its definition is valid over every
commutative topological ring; the following measure results specialize to the
local-field hypotheses above.
`measurePreserving_rightWeylInverseTranspose` composes the published preservation
of GL Haar by `iota` with right multiplication by `w`. The integral substitution
`integral_rightWeylInverseTranspose` follows from this measure-preserving
homeomorphism and applies even to the total Bochner integral without an
integrability hypothesis.

The subgroup automorphism `alpha(u) = w * iota(u) * w` is the published
`Whittaker.reflectedUnipotent`. Its normalized-Haar preservation is imported from
`RankOneMatrixFunctionalEquationComparisonReflectedHaar`, whose import closure
uses scalar Fourier and measure theory without the adjacent-rank model-star,
gamma/L or multiplicativity results. The unsigned identity `w² = 1` gives
`iota(h*u) * w = (iota(h)*w) * alpha(u)`.
`integral_rightWeylInverseTranspose_right_orbit` makes that substitution in the
unipotent integral, with no normalization factor.

Finally, `adjacentRank_integral_eq_of_reflected_right_averages` states the adapter
used by the model-star proof. If continuous compactly supported functions `f,q`
and a constant `c : ℂ` satisfy

```text
∫_N f(h*u) du = c * ∫_N q((iota(h)*w)*u) du    for every h,
```

then `∫_GL f = c * ∫_GL q`. Apply the right-orbit comparison to `f` and
`q ∘ (h ↦ iota(h)*w)`, then use the ambient Haar substitution above. This is an
internal consequence of published quotient integration and Haar symmetries; it
adds no equality or measure hypothesis to the eventual closed model-star target.
