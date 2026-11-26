# Square integrability of adelic induced convolution

`Langlands.Global.AdelicGroupPoints.InducedConvolutionWeightedSquareStatement` proves preservation
of the weighted integrability condition in `IsSquareIntegrableInducedForm`. It takes a continuous
inducing function invariant on the parabolic quotient and equivariant under the split component
by the half-modulus character. It uses the given Iwasawa compact, the geometric radical and the
Levi with the parabolic multiplication isomorphism. The conclusion holds at every complex
parameter for a continuous compactly supported kernel.

## Implemented proof

For an inducing function `v`, the normalized Levi value at `g` and `[m]` is
`m^{−ρ_P} v(mg)`. The rational Levi invariance and the split-component covariance make this
expression descend to a continuous function on `G(𝔸) × [M]`. Its squared norm is exactly the
integrand with the weight `|m^{−2ρ_P}|` used by `IsSquareIntegrableInducedForm`.

At the output argument `mk`, left invariance of Haar measure moves the right translation by
`k` to the kernel. The normalized convolution is then the integral of
`φ(k⁻¹z) z^λ m^{−ρ_P} v(mz)`. Compact-factorization Haar integration writes `z = qk′` with
`q` in the parabolic image and `k′ ∈ K`. The translated kernel vanishes outside a fixed compact
set of parabolic coordinates, the preimage of `K · supp φ · K⁻¹`. The kernel and the height factor
are bounded on the relevant compact sets.

At a fixed parabolic coordinate `q`, write its Levi component as `a`. Normality of the radical
and left unipotent invariance turn `v(mqk′)` into `v(mak′)`. The normalized square is the input
normalized square evaluated at `[ma]`, multiplied by the modulus factor at `a`. The canonical
measure of `[M]` is invariant under this right translation. The modulus factor is continuous in
`q` and integrable over the compact parabolic set. Fubini therefore proves square integrability
of the full convolution kernel on the product of the output space `K × [M]` and the compactly
restricted parabolic and compact integration variables. Cauchy–Schwarz for the finite integration
measure then gives square integrability of the integral itself. All output weights and measures
are those of `IsSquareIntegrableInducedForm`.

## Provenance

The norm and the Iwasawa integration calculation use J. Arthur, *An introduction to the trace
formula*, §7, printed pp. 32–33 (PDF pp. 44–45). The volume is registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`. The proof uses the Library's
half-modulus convention for the inducing functions and its canonical Levi quotient measure.
Compact-factorization Haar integration and the explicit bound give the square-integrability
step in `InducedConvolutionFiniteSpanStatement`.
