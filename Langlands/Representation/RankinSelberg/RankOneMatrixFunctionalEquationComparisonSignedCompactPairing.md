# Compact pairing with the actual signed Fourier orbit

This internal derived module proves an exact, convergent pairing identity for
an actual compact standard-character induced function. It retains every
canonical `F : PadicField.{uF} p` with prime `p`, every unitary additive
character `ψ`, every supplied self-dual additive Haar measure `ν`, and every
natural `n`, including zero. Write `r = n+1`, `χ = standardCharacter ψ n`,
`W = rankOneSignedWeyl n`, and `d_s(g) = determinantWeight abv g s`.
Every displayed group integral uses the existing unchanged unipotent or
general-linear Haar measure. Fourier is the plus rectangular integral with
that same `ψ,ν`.

For an actual compact induced function `f` and arbitrary complex `s`,
`weightedCompactMatrixLift` is the fixed supported matrix lift of
`weightedCompactFunction abv hopen n χ s f`. The canonical normalized
absolute value supplies `hopen`. This chooses one full-matrix
Schwartz–Bruhat function `Φ_s`, before any second test is supplied.
`weightedCompactMatrixLift_support` places its topological support inside
the invertible matrix locus. `weightedCompactMatrixLift_orbit_integrable`
proves convergence of the inverse-character unipotent orbit at every `g`.
`weightedCompactMatrixLift_orbit` states exactly

```text
d_s(g) ∫_N χ(u)^(-1) Φ_s((u g).val) du = f(g).
```

The proof applies the existing supported compact synthesis to the inverse
determinant twist of `f`, then cancels the two nonzero determinant-power
characters. Compactness here is projected support modulo the actual
upper-unipotent group, as in `Induction.CompactFunctions`.

`integral_signedUnipotentDualKernel_eq_weightedOrbit` identifies the inner
signed dual kernel with `weightedSignedMatrixOrbit` of the actual rectangular
Fourier transform, multiplied by the second test. It follows from evaluation
of `rectangularFourierEquiv`, actual group-to-matrix multiplication, and
linearity of the total Bochner integral. No convergence is asserted by this
identity alone. `integral_signedUnipotentShearedKernel_eq_compactPairing`
uses the preceding reconstruction with `s=r` to identify the inner sheared
original kernel with `f(g) Fourier(Ψ)((W g).val)` at every group point.

`signedFourierOrbitOfCompact` is the literal function

```text
K_f(g) = d_r(g) ∫_N χ(u)^(-1)
                  Fourier(Φ_r)((iota(u) W^(-1) g).val) du.
```

The lift `Φ_r` is the single supported lift already defined. The output is
not asserted compact. The theorems with suffixes `_left`,
`_locallyConstant`, and `continuous_signedFourierOrbitOfCompact` prove its
standard-character left covariance, local constancy and continuity using
SignedOrbitSmooth. In particular its covariance is for `χ`, with exactly
the signed inverse-transpose argument shown above.

`integrable_compact_signedWeyl_fourier_pairing` proves convergence of
`f(g) Fourier(Ψ)((W g).val)` for every second matrix Schwartz test `Ψ`.
It integrates the genuinely integrable sheared product kernel over the
unipotent coordinate and invokes the pointwise reconstruction identity.
It requires no box support condition on `Ψ`.

`compact_signedFourier_pairing` assumes additionally
`tsupport Ψ ⊆ RankOneBox.box F A q a` with `a>0`, for arbitrary integers
`A,q`. It proves convergence of both displayed GL integrands and equality

```text
∫_GL K_f(g) Ψ(g.val) dg = ∫_GL f(g) Fourier(Ψ)((W g).val) dg.
```

The proof starts from SignedGLFourier's actual product convergence and exact
exchange for `Φ_r,Ψ`. HaarShear substitutes `X=u g` on the original side,
without changing either Haar measure or introducing a scalar. Fubini applies
to the two proved product integrabilities; the two pointwise inner-integral
identities then give the stated equality. Integrability is obtained from
these product bounds, not inferred from equality of totalized integrals.

The provenance is a source-free derivation from SupportedSynthesis,
WeightedSynthesis, SignedOrbitSmooth, HaarShear and SignedGLFourier. The
accompanying SupportedSynthesis edit only names its twelve canonical local
instances to permit joint import with FramedIntegrability; all their values
and all its mathematics remain unchanged. This module proves no principal
averaging extraction, arbitrary-model extension, matrix functional equation
or gamma comparison.
