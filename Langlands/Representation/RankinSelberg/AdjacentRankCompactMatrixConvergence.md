# Uniform large-real-twist convergence on compact square-matrix tests

This derived internal module defines `AdjacentCompactMatrix.realTwistThreshold`
and proves its integrability API. Fix the canonical data of a prime-adic field
`F`, a unitary additive character `ψ`, a representation `σ` of `GL_(r+1)(F)`
of full standard Whittaker type, a specified Whittaker functional `ℓ`, and an
arbitrary continuous base quasicharacter `χ₀`. The field and representation
carrier universes are independent, and every natural `r`, including zero, is
allowed. There is no topology or norm on the original representation carrier.
The coefficient vectors belong to the actual image of its coefficient map.
Neither irreducibility, injectivity of that map, nor nonvanishing of `ℓ` is
needed for this convergence result.

Write `N = coefficientDeterminantOrder F ψ σ hσ ℓ` and
`c = characterNormExponent F χ₀`. The real-valued definition is

`realTwistThreshold = N - c + (r+1) - r/2`.

It is a sufficient threshold, with no minimality assertion. In particular it
is chosen before the real twist `u`, coefficient vector `W`, and square-matrix
Schwartz–Bruhat test `Φ`. For every `u` strictly above it,
`integrable_realTwist_of_threshold` proves genuine integrability of

`g ↦ Φ(g.val) W(g⁻¹) χ_u(det g) |det g|^(r/2)`

against the actual `generalLinearHaar F.Carrier r` on `GL_(r+1)(F)`.
`exists_integrable_realTwist_bound` packages the same result with the real
bound preceding all three quantifiers. The determinant weight is the existing
complex `determinantWeight` evaluated at the real exponent `r/2`. The proof
retains the supplied scalar additive Haar measure `ν`; a self-duality
certificate is unnecessary for this particular convergence criterion.

The definition `realTwistedCharacter` is literally the continuous character
`χ₀` multiplied by `unramifiedCharacterContinuous` evaluated at
`LocalFactor.spectralParameter q hq (u : ℂ)`, exactly the spectral family in
the adjacent-rank image statement. The lemma `norm_realSpectralCharacter`
uses that parameter's value `q^(-u)`, integer valuation powers, and
`|a| = q^(-ord a)` to prove that its norm is `|a|^u`.

For the arbitrary base character, `exists_character_norm_exponent` first
composes it with the determinant on `GL_1(F)`. The imported
`isOpen_ker_of_continuous_complex_character` makes this character's kernel
open. Pulling the kernel back along the continuous scalar embedding of
`Fˣ` into `GL_1(F)` shows that the kernel of `χ₀` is open. The published
`PadicField.TopologicalData.smoothCharacterNormDecomposition` then supplies
a real exponent `c` with `‖χ₀(a)‖ = |a|^c`.
`characterNormExponent` chooses such an exponent, and its `_spec` lemma
records this equality. Multiplication of norms gives
`norm_realTwistedCharacter`: `‖χ_u(a)‖ = |a|^(c+u)`.
The two determinant-weight lemmas record the corresponding real norm formula
and addition of complex exponents at the strictly positive determinant norm.

The general theorem `integrable_of_compact_det_growth` takes any continuous
complex GL function `f` with a natural determinant-pole order `N`: on each
compact square-matrix set, `‖f(g)‖ |det g|^N` has a nonnegative uniform bound.
For any continuous character with norm `|a|^c` and any real `s` satisfying
`N + (r+1) ≤ c+s`, it proves integrability of
`Φ(g.val) f(g) χ(det g) |det g|^s` against the same GL Haar measure.
Its proof sets `t = s-(r+1)` and `e = c+t-N ≥ 0`. The residual function

`A(g) = Φ(g.val) f(g) χ(det g) |det g|^t`

is continuous on GL and zero outside the compact square-matrix support of
`Φ`. Its norm factors as

`‖A(g)‖ = ‖Φ(g.val)‖ (‖f(g)‖ |det g|^N) |det g|^e`.

The first factor is bounded on that compact set, the second has the assumed
bound, and the final factor is a continuous function of all square matrices,
including singular ones, because `e ≥ 0`. It too is bounded on the compact
set. The imported `integrable_natWeight_of_compact_bound` therefore proves
integrability of `|det g|^(r+1) A(g)` by measurable zero extension and the
published GL/additive determinant-density equivalence. Addition of complex
exponents identifies this with the asserted integrand. The proof never
assumes continuity of a zero extension at singular matrices.

Finally, the specialization takes `f(g) = W(g⁻¹)`, uses
`glModelFunction_continuous` with the smoothness contained in the full
Whittaker-type hypothesis, and supplies the compact determinant-pole bound
from `coefficientDeterminantOrder_spec`. It takes the exact real spectral
twist, its proved norm exponent `c+u`, and `s=r/2`. The stated threshold
implies the general theorem's required inequality uniformly in `W` and `Φ`.

The provenance is internal derivation from the imported coefficient-growth,
measurable-extension, Haar-density, continuous-character, and real/complex
power results. This module establishes the square-matrix GL integral
criterion. It does not construct the induced Whittaker functional or prove
the adjacent-rank equality of whole coefficient and tensor-integral images;
those require the separate section, Jacquet-integral, and spanning arguments.
