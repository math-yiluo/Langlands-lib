# The Gram identity for wave packets of `L̂` from Lapid's inner product formula

Module `Langlands.Global.AdelicSymmetricFamilyGram` states and proves the
proposition `Langlands.Global.SymmetricFamilyGramBridgeStatement`:

`WavePacketInnerProductStatement →
IntertwiningSquareIntegrableExpansionStatement →
InducedRestrictionMemLpStatement → SymmetricFamilyGramStatement`.

The theorem `symmetricFamilyGramBridge` proves it. The four propositions are:

- `WavePacketInnerProductStatement`, published in module
  `Langlands.Global.AdelicWavePacketInnerProductStatement` (Lapid 2011,
  Proposition 2, formula (4)). For two presented parabolics `P`, `P'`,
  finitely many `v j ∈ A^2_P`, `v' j ∈ A^2_{P'}`, smooth compactly supported
  `c j`, `c' j`, continuations `E`, `E'` of the Eisenstein series holomorphic
  near the imaginary axis, an enumeration `T` of `Ω(P, P')`, and expansions
  `M(w_t, λ) v j = ∑ i, coeff t j i λ • ψ t j i` in `A^2_{P'}` with one length
  `m` and one domain `DM ⊇ i(X^*(P) ⊗ ℝ)`, it says that the wave packets
  `Θ = ∫ ∑ j, c j(x) E j(i e(x))` and `Θ'` are square integrable on
  `G(F) \ G(𝔸)` and that
  `∫ Θ · conj Θ' = ∫ ∑ t, ∑ j, ∑ i, ∑ j', c j(x) coeff t j i (i e(x))
  conj(c' j'(w_t x)) (ψ t j i, v' j')_{P'} dx`.
- `IntertwiningSquareIntegrableExpansionStatement`, in module
  `Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement`
  (Lapid 2011, §2, p.312, Working hypothesis). For `φ ∈ A^2_P` and
  `w ∈ Ω(P, Q)` it gives an expansion
  `M(w, λ)φ = ∑ i, coeff i λ • ψ i` with `ψ i ∈ A^2_Q`, valid for `Re λ`
  sufficiently regular, whose coefficients are meromorphic in coordinates
  with one domain of holomorphy containing `i(X^*(P) ⊗ ℝ)`. Lapid states
  the working hypothesis for standard parabolics and one maximal compact `K`
  in good position. The premise assumes it for all presented parabolics and
  every maximal compact `K` with the Iwasawa decompositions. This extension
  is an assumption of the premise, explained in its Markdown, and does not
  come from the source.
- `InducedRestrictionMemLpStatement`, in module
  `Langlands.Global.AdelicInducedRestrictionMemLpStatement`. The restriction
  of an element of `A^2_P` to `K × M(F) \ M(𝔸)` is square integrable for the
  measure of `H_P`.
- `SymmetricFamilyGramStatement`, in module
  `Langlands.Global.AdelicSpectralTransformInputs`, one of the inputs of the
  reduction of `SpectralTransformStatement`. For smooth compactly supported
  families `Φ`, `Φ'` of Arthur's space `L̂` (`symmetricFamilySpace`,
  `IsSmoothCompactFamily`) with Eisenstein continuations `E`, `E'`
  (`IsEisensteinContinuation`), the wave packet sum `W` of `(c, E)` is square
  integrable on `G(F) \ G(𝔸)` and `∫ conj(W) W' = ⟨Φ, Φ'⟩_{L̂}`, where `W'` is
  the wave packet sum of `(c', E')`.

The bridge is a theorem about these four Library propositions. It claims
nothing about whether its premises hold. None of them is proved in the
Library; the second and third are premises introduced for this reduction (see
their Markdown).

## Provenance

The bridge is internal to the Library. Its conclusion is the polarized form
of Lapid's Theorem 2 (Lapid 2011, §3, p.314, PDF page 323, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`; Arthur 2005,
Theorem 7.2 (b); Getz–Hahn (10.22)–(10.24)). Lapid writes "We conclude the
following result" after Proposition 2 and gives no further details; he uses
the weights `|𝒫(M_P)|⁻¹`. The statement here uses Arthur's normalization
`n_P = ∑_{P'} |Ω(P, P')|` (Arthur 2005, Theorem 7.2 (b), registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`). It enters through
`sum_card_div_card_eq_one` (module `Langlands.Global.AdelicWeylFamilyCounting`).

The derivation implemented here is the following. Proposition 2 computes the
inner product of two wave packets. The families are elements of `L̂`, so
their symmetry `Φ'_i(w_t λ) = M(w_t, λ) Φ'_{i'}(λ)` holds in `H_{P_i}` for
almost every `λ`. It turns the summand for `t` of Lapid's integrand into
`⟨Φ_i(w_t λ), Φ'_i(w_t λ)⟩`. A change of variables then gives
`|Ω(P_{i'}, P_i)| ∫ ⟨Φ_i, Φ'_i⟩`, and the weights `n_P⁻¹` cancel these
multiplicities.

## Proof

Write `μ_n = spectralMeasure n` and
`Θ_i = ∫ ∑ j, c i j x E i j (i e_i(x)) dμ_{n_i}(x)` (similarly `Θ'_i`), so that
`W = ∑ i, n_P(i)⁻¹ Θ_i` (`wavePacketSum`).

### Generic lemmas (section `Uniform`)

- `isOpenDenseInCoordinates_univ`, `isOpenDenseInCoordinates_iInter_of_finite`:
  the whole space and finite intersections of open dense sets are open and
  dense in coordinates.
- `isMeromorphicInCoordinatesOn_const_zero`: the zero function is meromorphic
  in coordinates on every domain of holomorphy of some meromorphic function.
- `exists_openDense_domain`: a finite family of functions meromorphic with
  domain `D` is meromorphic with an open dense domain `D' ⊇ D` (`D` itself
  if the family is nonempty, the whole space otherwise).
- `sum_fin_pad`: padding a sum over `Fin k` by zeros to `Fin m`, `k ≤ m`.
- `exists_uniform_expansions`: finitely many expansions
  `Mv s λ = ∑ q, coeff s q λ • ψ s q`, indexed by a finite type `S`, each of
  its own length and with its own domain containing a set `Z`, can be replaced
  by expansions of one common length `m` and with one common domain
  containing `Z`. The length is the maximum of the lengths. Missing
  coefficients are zero, and missing functions `ψ s q` are copied from an
  index where they exist, so every `ψ s q` keeps the property `Pr` (here:
  being in `A^2`). The common domain is the intersection of the enlarged
  domains of `exists_openDense_domain`, and the coefficients stay meromorphic
  on it by `IsMeromorphicInCoordinatesOn.congr_mono` (module
  `Langlands.Analysis.Meromorphic.CoordinateGluing`).
- `inner_sum_smul_map_sum_smul`: for a linear map `op` with
  `op (A' j) = ∑ q, a j q • Ψ j q`,
  `⟪∑ j', c j' • B j', op (∑ j, c' j • A' j)⟫ =
  ∑ j, ∑ q, ∑ j', c' j * a j q * conj (c j') * ⟪B j', Ψ j q⟫`.
- `integral_comp_of_measurePreserving`: change of variables along a
  measure-preserving map, with integrability.
- `integral_sum_eq_card_mul`: if `L t = g ∘ τ t` almost everywhere for
  measure-preserving maps `τ t`, `t ∈ κ`, then `∫ ∑ t, L t = |κ| ∫ g`.
- `piLp_L2_inner_eq`: in `PiLp 2 (fun i => Lp (H i) 2 ((c i)⁻¹ • ν i))`,
  `⟪f, g⟫ = ∑ i, (c i)⁻¹ ∫ ⟪f i y, g i y⟫ dν i`.
- `integral_conj_mul_eq_of_pairs`: for square integrable `Θ i`, `Θ' i`,
  `W = ∑ i, n(i)⁻¹ Θ i`, `W' = ∑ i, n(i)⁻¹ Θ' i`, if
  `∫ Θ' i' · conj(Θ i) = C(i', i) J(i)` and `∑ i', C(i', i) / n(i') = 1` for
  every `i`, then `∫ conj(W) W' = ∑ i, n(i)⁻¹ J(i)`.
- `measurePreserving_spectralMeasure_of_linearMap`: a linear map
  `ℝ^{n'} → ℝ^n` preserving Lebesgue measure has `n' = n`
  (`eq_of_measurePreserving_linearMap`, module
  `Langlands.Analysis.MeasurePreservingLinearCoordinates`) and preserves
  `spectralMeasure`.

### One pair of parabolics (section `Pair`)

The section variables are the data of `SymmetricFamilyGramStatement`, with
`nP` a variable.

- `wavePacket_pair_expansions`. For `i'`, `i` and `v' i' j ∈ A^2_{P_{i'}}`,
  `IntertwiningSquareIntegrableExpansionStatement` for
  `(P, Q) = (P_{i'}, P_i)` and `w = w i' i t` gives an expansion of
  `M(w_t, λ) v'_{i' j}` in `A^2_{P_i}` for every `(t, j)`, with domain
  containing `i(X^*(P_{i'}) ⊗ ℝ)`. `exists_uniform_expansions` with
  `S = T i' i × Fin (k' i')` makes their lengths and domains equal, as
  `WavePacketInnerProductStatement` requires.
- `wavePacket_pair_pointwise`. Fix `t`, `x` and `y = w_t x`, and assume the
  three almost-everywhere facts at `x`: `Φ'_{i'}(x)` is the class of the
  restriction of `∑ j, c' i' j x v' i' j`, `Φ_i(y)` is the class of the
  restriction of `∑ j, c i j y v i j`, and `Φ'_i(y) = M(w_t, x) Φ'_{i'}(x)`.
  Then the summand of Lapid's integrand for `t` at `x` equals
  `⟨Φ_i(y), Φ'_i(y)⟩`. The classes of the restrictions of `v`, `v'`, `ψ` are
  elements of `H_P` by `InducedRestrictionMemLpStatement`
  (`toLp_mem_inducedHilbertSpace`, module
  `Langlands.Global.AdelicInducedL2Inner`). `IsImaginaryIntertwiningOperator`
  applied to the expansion of `M(w_t, λ) v'_{i' j}` computes
  `M(w_t, x)` on the class of `v'_{i' j}`. Then
  `inner_sum_smul_map_sum_smul` expands the inner product, and
  `inner_eq_inducedInnerProduct` (same module) identifies the `L²` inner
  products of classes with `(ψ, v)_{P_i}`.
- `wavePacket_pair_inner_of_expansions`. Given such expansions,
  `WavePacketInnerProductStatement` for `(P, P') = (P_{i'}, P_i)` with the
  data `(c' i', E' i')` and `(c i, E i)` gives square integrability of
  `Θ'_{i'}` and `Θ_i` and Lapid's formula for `∫ Θ'_{i'} conj(Θ_i)`. The
  coordinate change `τ_t : x ↦ e_i⁻¹(w_t e_{i'}(x))` preserves the measures
  `μ` (hypothesis `hw` and the last generic lemma). By
  `wavePacket_pair_pointwise`, the `t`-summand of the integrand is
  `⟨Φ_i, Φ'_i⟩ ∘ τ_t` almost everywhere. The almost-everywhere facts come
  from `IsSmoothCompactFamily`, from the quasi-measure-preservation of `τ_t`,
  and from the membership of `Φ'` in `symmetricFamilySpace`. Then
  `integral_sum_eq_card_mul` gives
  `∫ Θ'_{i'} conj(Θ_i) = |T i' i| ∫ ⟨Φ_i, Φ'_i⟩ dμ_{n_i}`. Here
  `⟨Φ_i, Φ'_i⟩` is integrable because `Φ_i, Φ'_i ∈ L²((nP i)⁻¹ • μ; H_{P_i})`
  with `nP i ≠ 0`.
- `wavePacket_pair_inner` combines the two previous lemmas.

### The main theorem

`symmetricFamilyGramBridge` introduces the data. It derives the square
integrability of restrictions from `InducedRestrictionMemLpStatement` and
`nP i ≠ 0` from `nonempty_self`. It then applies `wavePacket_pair_inner` to
every pair `(i', i)`. The pairs `(i, i)` give `Θ_i, Θ'_i ∈ L²`, hence
`W ∈ L²` as a finite sum. `integral_conj_mul_eq_of_pairs` with
`C(i', i) = |T i' i|`, `J(i) = ∫ ⟨Φ_i, Φ'_i⟩ dμ_{n_i}` and
`sum_card_div_card_eq_one` gives `∫ conj(W) W' = ∑ i, n_P(i)⁻¹ J(i)`, which
is `⟨Φ, Φ'⟩_{L̂}` by `piLp_L2_inner_eq`.

## Implementation notes

`wavePacket_pair_inner_of_expansions` and `wavePacket_pair_inner` raise
`maxHeartbeats` to `6400000`. Their statements are long. The proofs avoid
`rw` on large goals, which type-checks the whole motive, and use `exact` with
the generic lemmas instead. The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
