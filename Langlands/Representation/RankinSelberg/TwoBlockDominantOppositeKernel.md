# Opposite spectral kernels

This internal module supplies the explicit finite kernels for the complex
opposite-twist family. Its analytic and gamma continuation assertions assume
`1 < q`. The clearing kernel is the Laurent embedding of
`P₀(qᵘ X) P₁(q⁻ᵘ X)`, with the project's spectral-point convention.
At zero it is the Laurent embedding of `P₀ P₁`.

Each rescaled polynomial coefficient is a fixed scalar times an entire power
of a spectral point. The product coefficient is a finite sum of products of
these functions. Polynomial degree bounds give one common finite support
independent of the complex parameter. The published coefficientwise Laurent
specialization theorem therefore carries clearing on a real ray to clearing
at zero.

For two fixed rational gamma factors, the module rescales both factors with
opposite parameters. Their rescaled numerator and denominator products give
an exact presentation. Injectivity of polynomial rescaling proves that the
denominator product stays nonzero. For `gammaFE_oppositeSpectralProduct_at_zero`,
the independent clearing polynomials must also satisfy `P₀ * P₁ ≠ 0`.
This makes the clearing kernel at zero nonzero; it is a separate requirement
from nonvanishing of the gamma presentation denominator, which uses
`G₀.denom` and `G₁.denom`. Under these hypotheses, the published entire gamma
continuation theorem gives the functional equation at zero from entire
original and dual coefficient families, rational continuations, absolute
spectral expansions, real-ray clearing, and real-ray functional equations.

This is an internal adaptation of `AdjacentRankClearingKernel` and
`AdjacentRankSpectralGammaContinuation` to two opposite shifts. It does not
construct Whittaker families, prove real-ray bounds, or establish the final
dominant-rank factor statements.
