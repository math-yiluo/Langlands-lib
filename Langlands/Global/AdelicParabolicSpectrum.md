# The spaces `L²_P([G])` and `L²_disc([G])`

Module `Langlands.Global.AdelicParabolicSpectrum` defines the subspaces of
`L²([G])`, `[G] = A_G G(F) \ G(𝔸)`, that occur in Langlands' spectral
decomposition in the form of Getz–Hahn Theorem 10.5.1: the space
`(𝔞_M^G)^*` of a parabolic, the wave packets of Eisenstein series over
`i(𝔞_M^G)^*`, the closed span `L²_P([G])` of these wave packets, and the
discrete spectrum `L²_disc([G])`. It is a definition module and proves
nothing.

## Sources

- Getz–Hahn, *An introduction to automorphic representations*, registered
  as `getz-hahn-2024-automorphic-representations` (PDF page = printed
  page + 12 in chapters 9 and 10):
  - §9.1 (9.6), p.242: `L²_disc([G])` is the largest closed subspace of
    `L²([G])` that is a Hilbert direct sum of irreducible
    subrepresentations.
  - §10.5 (10.21)–(10.24), pp.281–282: for an association class `𝒫`, the
    families `F_P : i(𝔞_M^G)^* → Ind_P^G(L²_disc([M]))`, `P ∈ 𝒫`, with the
    Weyl invariance condition, the integral
    `∑_{P ∈ 𝒫} n_P⁻¹ ∫_{i(𝔞_M^G)^*} E(x, F_P(λ), λ) dλ` (10.24), and
    `L²_𝒫([G])`, the closure of the span of these integrals for compactly
    supported `F`. For `P = G`, `(𝔞_G^G)^* = 0` and
    `L²_G([G]) = L²_disc([G])`.
- J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4
  (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, Theorem 7.2(b),
  printed p.35 (PDF page 47): the same construction on
  `L²(G(F) \ G(𝔸))` and `i𝔞_P^*`. The map `F ↦ (10.24)` is defined when
  each `F_P` is a smooth compactly supported function with values in a
  finite-dimensional space of `K`-finite, `Z`-finite vectors. It extends to
  a unitary map onto the closed subspace `L²_𝒫`.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §2 p.311 and
  §3 p.314: `A^2_P`, the Eisenstein series `E(φ, λ)` and the wave packets
  `Θ_{P,φ} = ∫_{i𝔞_P^*} E(φ(λ), λ) dλ`.

## Existing objects used

- `RealCharacterParameter F P = X^*(P) ⊗ ℝ` (`𝔞_P^*`), `realParameterPairing`,
  `characterLog F P` (`H_P`, with `⟨χ, H_P(x)⟩ = log |χ(x)|_𝔸`) and
  `imaginaryParameter F P` (`μ ↦ iμ`), modules
  `Langlands.Global.AdelicComplexParameters`,
  `Langlands.Global.AdelicCharacterLog` and
  `Langlands.Global.AdelicSquareIntegrableInducedForms`.
- `RestrictionSplitCentre.canonicalSubgroup F G` (`A_G`, the positive real
  points of the chosen split component of `Res_{F/ℚ} G`),
  `RestrictionSplitCentre.CanonicalQuotient F G` (`[G]`),
  `RestrictionSplitCentre.canonicalMeasure F G` and
  `RestrictionSplitCentre.canonicalL2RightAction F G`, module
  `Langlands.Global.AdelicRestrictionSplitCentreCanonical`.
- `IsSquareIntegrableInducedForm` (Lapid's `A^2_P`),
  `IsIwasawaCompact.eisensteinSeries`, `ParabolicRootPresentation` and
  `IsRegularParameter`, as in `WavePacketInnerProductStatement` and
  `WavePacketCompletenessStatement`; `spectralMeasure n`, the measure
  `(2π)^{-n} dx` on `ℝⁿ` (module `Langlands.Global.AdelicInducedInnerProduct`).
- `centralSplitTorusCharacter` (module
  `Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof`), the
  proved hypothesis of `canonicalL2RightAction`.
- `Langlands.Analysis.discretePart` (module
  `Langlands.Representation.Unitary.DiscretePart`).

## Definitions

- `relativeParameterSpace p`: for `p : P → G`, the real subspace of
  `X^*(P) ⊗ ℝ` of the `μ` with `⟨μ, H_P(x)⟩ = 0` for every `x ∈ P(𝔸)` with
  `p(x) ∈ A_G`. Since `A_G` is central it lies in every parabolic, and
  `H_P(A_G)` is the subspace `𝔞_G` of `𝔞_P = 𝔞_M`. So this is the annihilator
  of `𝔞_G` in `𝔞_M^*`, that is, `(𝔞_M^G)^*`. For `P = G` it is `0`.
- `IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ`: for a
  parabolic `p : P → G` with Levi `l`, the subgroup `iU`, a presentation `r`
  and `hK : IsIwasawaCompact p K` (`P(𝔸)K = G(𝔸)`), there are coordinates
  `e : ℝⁿ ≃ (𝔞_M^G)^*`, finitely many `v j ∈ A^2_P`, smooth compactly
  supported `c j : ℝⁿ → ℂ`, and functions `E j` on `X^*(P) ⊗ ℂ` with a common
  set `D ⊇ i𝔞_P^*` such that, for every `g`, `λ ↦ E j λ g` is meromorphic
  with domain of holomorphy `D`, `E j` equals `hK.eisensteinSeries (v j)` for
  `Re λ` sufficiently regular, and
  `Θ(g) = ∫ ∑ j, c j x · E j (i e(x)) g d(spectralMeasure n)(x)`.
- `parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT`: the topological
  closure in `L²([G])` (`Lp ℂ 2 (canonicalMeasure F G)`) of the span of the
  classes `f` with `f = Θ ∘ out` almost everywhere, `Θ` a wave packet as
  above. Here `out` chooses a representative in `G(𝔸)` of a point of `[G]`.
- `discreteSpectrum F G hG`: `discretePart` of the right regular
  representation `canonicalL2RightAction F G` of `G(𝔸)` on `L²([G])`.

## Correspondence with the source

- Wave packets live on `[G]`. Lapid's `A^2_P` condition gives
  `φ(ag) = δ_P(a)^{1/2} φ(g)` for `a ∈ A_M`, and `δ_P = 1` on the central
  subgroup `A_G ⊆ A_M`. So for `λ ∈ i(𝔞_M^G)^*` the Eisenstein series
  satisfies `E(φ, λ)(ag) = e^{⟨λ, H_P(a)⟩} E(φ, λ)(g) = E(φ, λ)(g)`. It is
  also left `G(F)`-invariant, so the wave packets are functions on `[G]`
  and `Θ ∘ out` does not depend on the choice of representatives. When `Θ`
  is not square integrable, it contributes nothing to the span; by Lapid's
  Theorem 2 every wave packet is square integrable. These remarks are
  explanatory and not proved here.
- Single parabolics instead of families. GH and Arthur span `L²_𝒫` by the
  integrals (10.24) of Weyl-invariant families over all `P ∈ 𝒫`. Each term
  `∫ E(x, F_P(λ), λ) dλ` of such a family, with `F_P` smooth, compactly
  supported and with values in a finite-dimensional subspace of `A^2_P`, is
  a wave packet of `P` in the present sense: write `F_P = ∑ j, c j · v j` in
  a basis `v j`. Conversely, a wave packet of one `P ∈ 𝒫` is the integral
  (10.24) of its symmetrization
  `F_{P'}(λ) = ∑_{s ∈ W(𝔞_M, 𝔞_{M'})} M(s, s⁻¹λ) φ(s⁻¹λ)`, by the
  functional equation and `∑_{P'} |W(𝔞_M, 𝔞_{M'})| = n_P` (Delorme 2023,
  Lemma 6.2, registered as `delorme-2023-spectral-theorem-langlands`). So the
  closed span of (10.24) over compactly supported smooth families is the
  closed span of the wave packets of all `P ∈ 𝒫`. Arthur's unitary
  extension shows that the measurable families of GH give the same closure.
  `parabolicSpectrum` is the closed span for one presented `P`;
  `SpectralDecompositionStatement` asserts that, for parabolics containing
  a fixed minimal parabolic `P₀` with `P₀(𝔸)K = G(𝔸)` (GH's and Arthur's
  standard parabolics), it depends only on the association class of `P`, so
  it equals `L²_𝒫([G])`. This is explanatory and not proved here.
- Inducing data. The `v j` range over all of `A^2_P`, the `K`-finite
  automorphic vectors of `Ind_P^G(L²_disc([M]))`, not only over cuspidal
  data. The continuations `E j` are required to be holomorphic on all of
  `i𝔞_P^*`, not only on `i(𝔞_M^G)^*`. By Lapid's Proposition 6
  (`EisensteinImaginaryAxisHolomorphyStatement`) this holds for every
  element of `A^2_P`, so no inducing data are lost. Any `(E, D)` agreeing
  with the Eisenstein series for `Re λ` sufficiently regular gives the same
  `Θ`, since `E j` is meromorphic on the whole connected space
  `X^*(P) ⊗ ℂ`.
- Coordinates and measures. The span does not depend on the coordinates `e`
  or on the normalization of `dλ`: changing them changes `c j` by a smooth
  change of variables and a positive constant. The measure on `[G]` only
  affects the inner product by a positive constant, so the closed subspaces
  and their orthogonality do not depend on it.
- The subgroup `iU` and the Levi `l` are parameters. The definitions do not
  require `iU` to be the unipotent radical of `P`; statements using them,
  such as `SpectralDecompositionStatement`, add
  `LeviSubgroup.IsGeometricUnipotentRadical iU`. The presentation `r`
  makes `p` parabolic and `l` a rational Levi subgroup.
- `L²_disc`. `discretePart` is the closure of the sum of the irreducible
  closed invariant subspaces. For the unitary representation on `L²([G])`
  this is GH's largest closed subspace that is a Hilbert direct sum of
  irreducible subrepresentations (see the Markdown of
  `Langlands.Representation.Unitary.DiscretePart`).
- For `P = G`, `(𝔞_G^G)^* = 0`, `n = 0` and `spectralMeasure 0` is the unit
  point mass. The regularity condition on `λ` is then vacuous, so a wave
  packet is a finite sum `∑ j, c j · v j` of square-integrable automorphic
  forms on `[G]`. That their closed span is `L²_disc([G])`, which GH obtain
  by definition, is a theorem; `SpectralDecompositionStatement` includes it.
