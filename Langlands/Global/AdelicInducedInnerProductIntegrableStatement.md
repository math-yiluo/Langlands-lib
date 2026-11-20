# Absolute convergence of the inner product `(·,·)_P` on `A^2_P`

Module `Langlands.Global.AdelicInducedInnerProductIntegrableStatement` defines
the proposition `Langlands.Global.InducedInnerProductIntegrableStatement`. It
supplies no proof.

## Sources and provenance

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §2, printed
  p.311 (volume PDF page 320). Lapid defines `A^2_P` as the subspace of
  `A^n_P` of the `φ` with
  `‖φ‖²_P = ∫_{A_M U(𝔸) M(F) \ G(𝔸)} |φ(g)|² dg < ∞`, and uses the inner
  product `(φ, ψ)_P` of this Hilbert norm.

The statement is derived. Lapid takes for granted that the integral defining
`(φ, ψ)_P` converges absolutely for `φ, ψ ∈ A^2_P`. That follows from the
Cauchy–Schwarz inequality, `|φ ψ̄| ≤ ½(|φ|² + |ψ|²)`. The statement records
this fact for the Iwasawa form `inducedInnerProduct` of the published module
`Langlands.Global.AdelicInducedInnerProduct`, in which a compactly supported
weight `β` replaces the integral over `A_M`. It is the integrability premise
needed to expand `inducedInnerProduct` by sesquilinearity, which the proof of
`Langlands.Global.WavePacketIsometryStatement` uses (see
`Langlands.Global.AdelicWavePacketIsometryReduction`). The task contract of
that proof lists the integrability of `inducedInnerProduct` on the spans
involved as an expected prerequisite.

## Statement

The data are those of one member of the family in
`WavePacketIsometryStatement`, for a number field `F : Type`:

- `G` connected reductive, a parabolic `p : P → G` with geometric unipotent
  radical `iU`, Levi `l`, presentation `r : ParabolicRootPresentation p l a`
  of its split component, and Levi projection `π` with `l ≫ π = 𝟙`. All
  groups are affine and `M` is locally of finite type; `P` is locally of
  finite type as a closed subgroup, supplied by `haveI`.
- `K` maximal compact with `hK : IsIwasawaCompact p K` (that is,
  `P(𝔸)K = G(𝔸)`), a closed matrix embedding `rho`, and the smooth-structure
  data `hsmooth`, `hcalc`.
- A Haar measure `μM` on `M(𝔸)` with
  `IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM`.
- Coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and a continuous compactly supported
  `β : ℝⁿ → ℝ`.
- `φ, ψ ∈ A^2_P`, that is
  `IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l`.

The conclusion is that the function

`(k, x) ↦ β(y(m)) · m^{-2ρ_P} · φ(m k) · conj ψ(m k)`, with `m = x.out`,

on `K × M(F) \ M(𝔸)` is integrable (`MeasureTheory.Integrable`) for the
product of `compactHaarProbability F G K hK.isCompact` on `K` and the
quotient `LeftCosetSpace.discreteQuotientMeasure` of `μM` by counting measure
on `M(F)`. Here `y(m) = parameterCoordinates F P e (characterLog F P (l m))`.
This integrand and measure are exactly the ones in the definition of
`inducedInnerProduct K hK.isCompact p l μM e β φ ψ`, which iterates the two
integrals. Integrability over the product is the absolute convergence that
justifies Fubini's theorem and linearity in each argument.

## Correspondence with the source

- The integrand. `m^{-2ρ_P}` is `δ_P(m)⁻¹`, as explained in the Markdown of
  `Langlands.Global.AdelicSquareIntegrableInducedForms`. Iwasawa coordinates
  `g = u m k` turn Lapid's integral over `A_M U(𝔸) M(F) \ G(𝔸)` into
  `∫_K ∫_{A_M M(F) \ M(𝔸)} δ_P(m)⁻¹ φ(m k) conj ψ(m k) dm dk`. The Markdown
  of `AdelicInducedInnerProduct` explains how the weight `β(y(m))` on
  `M(F) \ M(𝔸)` replaces the quotient by `A_M`.
- Why it should hold. `IsSquareIntegrableInducedForm` requires that
  `(k, m) ↦ δ_P(m)⁻¹ |φ(m k)|²` is integrable on `K × [M]`, where
  `[M] = A_M M(F) \ M(𝔸)` carries `RestrictionSplitCentre.canonicalMeasure`.
  For `a ∈ A_M`, the `A^n_P` condition `φ(a g) = δ_P(a)^{1/2} φ(g)` makes
  `δ_P(m)⁻¹ |φ(m k)|²` invariant under `m ↦ a m`. Write `M(F) \ M(𝔸)` as
  fibred over `[M]` with fibre `A_M`, on which `y` is a linear coordinate
  through `H_P`. The integral of `|β(y(m))| δ_P(m)⁻¹ |φ(mk)| |ψ(mk)|` over the
  fibre through `m` is then at most
  `C · ½ (∫ |β|) · δ_P(m)⁻¹ (|φ(mk)|² + |ψ(mk)|²)`, where `C` depends only on
  the measures. Integrating over `K × [M]` gives a finite bound. This argument is explanatory and is not formalized here. It needs
  the comparison of `μM` with the product of `canonicalMeasure` and a Haar
  measure on `A_M`, and the injectivity of `H_P` on `A_M`.
- The hypotheses. They are the per-member hypotheses of
  `WavePacketIsometryStatement`, without the wave packet data. They make `P`
  a parabolic with Levi `M` and split component `A`, `K` a maximal compact
  in good position, and `μM` the Haar measure compatible with the Iwasawa
  decomposition. The statement uses neither `∫ β = 1` nor any property of
  `β` beyond continuity and compact support.

## Scope

Only integrability is asserted. The value of the integral, its independence
of `β`, the Cauchy–Schwarz bound and the comparison of measures are not
stated. The statement is not proved here.
