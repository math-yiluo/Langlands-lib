# Scalar p-adic Fourier scaling

Worker 1650 proves the existing `Langlands.LocalFactors.PadicFourierScalingStatement.{u}` as `Langlands.HarmonicAnalysis.padicFourierScaling`. The target is imported unchanged from `Langlands.LocalFactor.Harmonic.Statement`. The theorem retains every prime, field universe, supplied topology, continuous nontrivial additive character, additive Haar measure and locally constant compactly supported function.

This is an internal derivation from the published `padicScalarHaarScaling` and Mathlib's Bochner integral APIs. The source correspondence and plus-sign convention are those documented in the unchanged [target Markdown](../LocalFactor/Harmonic/Statement.md). No new literature result is assumed.

The private integral identity expands `Fourier.fourierIntegral ψ⁻¹` to the plus-sign kernel `ψ(x*y)`: character inversion negates its argument, cancelling the Fourier definition's negation.

For the image-set modulus, apply the published pushforward formula to the unit `a⁻¹` and evaluate the resulting measures on the supplied measurable set `s`. The inverse map's preimage is exactly the image of `s` under `a*x`. Multiplicativity of `T.normalizedAbsUnits` turns the inverse unit's inverse modulus into `T.normalizedAbs a`, converted to `ENNReal.ofReal` by nonnegativity. The imported scalar Haar theorem already derives the regularity needed for arbitrary supplied Haar measures.

Measure scaling is `integral_smul_nnreal_measure`, followed by the identification of nonnegative-real scalar action on complex numbers with multiplication. Character scaling expands `AddChar.mulShift_apply`; commutativity and associativity identify `a*(x*y)` with `x*(a*y)`.

For argument scaling, multiplication by the unit `a` is a measurable equivalence. Apply its unconditional `MeasurableEmbedding.integral_map` identity to `g(z) = ψ(z*(a⁻¹*y))*f(z)`. Commutativity and the unit inverse laws identify `g(a*x)` with `ψ(x*y)*f(a*x)`. The published scalar pushforward contributes `(T.normalizedAbsUnits a)⁻¹`; the scalar integral identity and coercion lemmas give exactly the target's real inverse factor and inverse argument.

These integral transformation identities hold for arbitrary functions under Mathlib's integral convention; restricting them to the target's test functions proves the requested laws without adding integrability or normalization premises. No inversion, dual-measure, self-dual-measure or epsilon-factor conclusion is asserted here.
