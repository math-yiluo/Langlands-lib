# Completeness of wave packets of Eisenstein series

Module `Langlands.Global.AdelicWavePacketCompletenessStatement` states
`Langlands.Global.WavePacketCompletenessStatement` as a proposition
definition. It supplies no proof.

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, arXiv:2006.12893
  (2023 version), registered as `delorme-2023-spectral-theorem-langlands`
  (folder with the PDF and the TeX source; numbers below are those of the
  PDF):
  - Theorem 6.1 (PDF page 22): Lapid's Theorem 2. For standard parabolics
    `P`, the space `𝒲_P` of compactly supported smooth functions on `i𝔞_P^*`
    with values in a finite-dimensional subspace of `𝒜²_P`, the wave packets
    `Θ_{P,φ}`, the Hilbert space `ℒ` of families `(F_P)` with the symmetry
    condition (6.2) and norm `∑_P |𝒫(M_P)|⁻¹ ‖F_P‖²_*`, its subspace `ℒ'` of
    families with `F_P ∈ 𝒲_P`, and the map
    `ℰ : (F_P) ↦ ∑_P |𝒫(M_P)|⁻¹ Θ_{P,F_P}` on `ℒ'`, which extends to an isometry
    `ℰ̄` from `ℒ` to `L²(G(F) \ G(𝔸))`.
  - Lemma 6.2 (PDF page 22): the wave packets of Proposition 5.4 lie in the
    image of `ℰ`, by symmetrizing over `W(P|Q)` and the functional equation
    of the Eisenstein series.
  - Theorem 7.9 (PDF page 33): the image of `ℰ̄` is equal to
    `L²(G(F) \ G(𝔸))`.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, p.314 (PDF
  page 323), after Theorem 2: "Of course, Langlands showed that `E` is onto
  as well."
- J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4
  (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, Theorem 7.2 (b)
  and (7.5), printed p.35 (PDF page 47); Getz–Hahn, registered as
  `getz-hahn-2024-automorphic-representations`, Theorem 10.5.1, p.282 (PDF
  page 294): the same decomposition, proved by Langlands.

## Statement

The data, for a number field `F : Type`: `G` connected reductive; a maximal
compact subgroup `K` of `G(𝔸)` such that `P₀(𝔸)K = G(𝔸)` for some minimal
parabolic `p₀ : P₀ → G` (`IsMinimalParabolicSubgroup`, `IsIwasawaCompact`);
a closed matrix embedding `rho`; the smooth-structure data `hsmooth`,
`hcalc`. Let `μG` be the quotient of Mathlib's Haar measure on `G(𝔸)` by
counting measure on `G(F)`, and `f : G(F) \ G(𝔸) → ℂ` with
`MemLp f 2 μG`.

Hypothesis: `f` is orthogonal to every wave packet. A wave packet is given
by the data of `WavePacketInnerProductStatement` for one parabolic:
a parabolic `p : P → G` with geometric unipotent radical `iU`, Levi `l` and
presentation `r : ParabolicRootPresentation p l a`, with
`hK : IsIwasawaCompact p K`; coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`;
`v j ∈ A^2_P` (`IsSquareIntegrableInducedForm`); smooth compactly supported
`c j : ℝⁿ → ℂ`; and continuations `E j`, meromorphic in every `g` with one
domain `D ⊇ i𝔞_P^*` and equal to `hK.eisensteinSeries (v j)` for `Re λ`
sufficiently regular. For all such data,
`∫ f(y) · conj (Θ(y.out)) dμG(y) = 0` with
`Θ(g) = ∫ ∑ j, c j x · E j (i e(x)) g d(spectralMeasure n)(x)`.

Conclusion: `f = 0` `μG`-almost everywhere.

## Correspondence with the source

- Density instead of surjectivity. `ℰ̄` is an isometry, so its image is
  closed and equals the closure of `ℰ(ℒ')`. The space `ℰ(ℒ')` lies in the
  span of the wave packets `Θ_{P,φ}`, `P` standard, `φ ∈ 𝒲_P`. Conversely
  every such `Θ_{P,ψ}` lies in `ℰ(ℒ')`: the argument of Lemma 6.2 applies to
  any `ψ ∈ 𝒲_P`. The family `F_Q(λ) = ∑_{s ∈ W(P|Q)} M(s, s⁻¹λ) ψ(s⁻¹λ)`
  is in `ℒ'`. The functional equation gives `Θ_{Q,F_Q} = |W(P|Q)| Θ_{P,ψ}`,
  and `∑_Q |W(P|Q)| = |𝒫(M_P)|` gives `ℰ((F_Q)) = Θ_{P,ψ}`. So Theorem 7.9
  says that the wave packets of standard parabolics span a dense subspace of
  `L²(G(F) \ G(𝔸))`. In a Hilbert space this is equivalent to the
  statement that a vector orthogonal to all of them is zero. This is
  explanatory and not proved here.
- All presented parabolics. The hypothesis asks for orthogonality to the
  wave packets of every parabolic with a presentation and with
  `P(𝔸)K = G(𝔸)`. Among them are all parabolics containing `P₀`, for which
  `P(𝔸)K ⊇ P₀(𝔸)K = G(𝔸)`, that is, Delorme's standard parabolics. The
  hypothesis is therefore at least as strong as orthogonality to the wave
  packets of standard parabolics, and the statement follows from Theorem 7.9
  together with the previous remark; no reduction of non-standard parabolics
  is needed.
- `𝒲_P`. As in `WavePacketInnerProductStatement`, `φ = ∑ j, c j · v j` in
  the coordinates `λ = i e(x)`, with `E(v j, ·)` holomorphic near `i𝔞_P^*`.
  By Lapid's Proposition 6 (`EisensteinImaginaryAxisHolomorphyStatement`)
  this holds for every element of `A^2_P`, so these are all of Delorme's
  `𝒲_P`. The continuations enter in universal form: any `(E, D)` agreeing
  with the Eisenstein series for `Re λ` sufficiently regular gives the same
  `Θ`.
- The compact subgroup. Delorme and Lapid fix `K` in good position with
  respect to a minimal Levi subgroup, for which `G(𝔸) = P₀(𝔸)K`. Here `K` is a
  maximal compact subgroup with this property for some minimal parabolic.
  Changing `K` is reduced to their case as in the Markdown of
  `EisensteinAbsoluteConvergenceStatement`. This is explanatory and not
  proved here.
- Inducing data. As Delorme requires, the inducing data range over all of
  `A^2_P`, the discrete spectrum of `M`, not only over cuspidal data.
- `L²(G(F) \ G(𝔸))`, the measure and the universe are those of
  `WavePacketInnerProductStatement`.

## Proof ingredients (explanatory)

Delorme's proof uses: Franke's notion of tempered automorphic forms and its
comparison with Bernstein's (§3); uniform temperedness of Eisenstein series
on bounded sets of unitary parameters (§4); wave packets in the
Harish-Chandra Schwartz space of Lapid 2013 (§5, after Franke §5.3); the
isometry of Theorem 6.1; and, if the image were not all of `L²`, a nonzero
tempered automorphic form orthogonal to all wave packets, obtained from
Bernstein's estimate on the support of the Plancherel measure (Lemma 7.10),
whose truncated inner products with Eisenstein series force it to vanish
(§7).

## Scope

The statement is the completeness of the wave packets. It does not state
the isometry (`WavePacketIsometryStatement`), the orthogonal decomposition
over associated classes (Arthur (7.5), Getz–Hahn Theorem 10.5.1), or a
description of the discrete spectrum.
