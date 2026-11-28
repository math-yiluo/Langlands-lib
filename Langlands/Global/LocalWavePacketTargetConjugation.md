# Transport of the truncated limit along rational conjugation of the second parabolic

Module `Langlands.Global.LocalWavePacketTargetConjugation`. It is a helper module for the proof
`Langlands.Global.truncatedWavePacketStandardization` and contains no statement of its own.

## Main result

`TruncatedWavePacketPairLimit.of_conj_target`: let `s` be a rational point of `G`, `t ∈ G(F)`
its adelic point and `p'' = p' ≫ Int(s)` the conjugate of the target parabolic subgroup (same
`P'`, `M'`, `U'`, `l'`, `π'`). Assume `G` is connected reductive, the source unipotent radical
`U` is unipotent, and `p'` has a root presentation `r'` with geometric unipotent radical `iU'`.
Then `TruncatedWavePacketPairLimit` for `(p, p')` gives it for `(p, p'')`, for the same compact
`K` and regularity predicates.

## Proof

Write `t = p''(q) k₀` (Iwasawa, `k₀ ∈ K`) and `q = u₀ m₀` with `u₀ ∈ U'(𝔸)`, `m₀ ∈ M'(𝔸)`
(`leviComponent`, `radicalComponent`). Given data for `p''`, define data for `p'`:

- forms `v'(g) = v''(t g)` and `ψ(g) = ψ''(t g)`. They are square integrable induced forms for
  `p'` by `IsSquareIntegrableInducedForm.of_conjugate_map`, applied to `p''` and `t⁻¹`;
- continuations `E'(λ) = q^{-λ} E''(λ)`, because
  `E_{p''}(v''(·), λ) = q^{λ} E_{p'}(v', λ)`. Here the Eisenstein series is the defining sum over
  the rational cosets (Bernstein–Lapid 2024, §2.2, (2.1)), and the scalar identity is the Library
  theorem `IsIwasawaCompact.eisensteinSeries_conjugate_parabolic`, which reindexes the rational
  cosets by left multiplication by `s` and compares the heights for the same `K`; `λ ↦ q^{-λ}` is
  entire;
- coefficients `c'(x) = c''(x) q^{i e'(x)}`, smooth with the same support, so the two wave
  packets are equal;
- Weyl representatives `s⁻¹ w''` (`IsWeylConjugation.of_conjugate_target`), the same `c`, and
  expansion coefficients `q^{wλ} coeff''(λ)`, because
  `M(s w, λ)φ(t g) = t^{-wλ} M(w, λ)φ(g)` (`intertwiningConjugateTarget`); `q^{wλ}` is a parameter
  power of `P` at the image of `q`, hence entire in `λ`;
- the Haar measure `δ_{P'}(m₀)⁻¹ μ''` on `M'(𝔸)`, where `δ_{P'}(m₀)⁻¹ = m₀^{-2ρ}`, and the weight
  `β'(z) = β''(z + y(m₀))`.

The right side of formula (4) is unchanged: the factors `q^{wλ}` and `conj(q^{iμ})` with
`iμ = wλ` purely imaginary cancel (`parameterPower_imaginaryParameter_mul_conj`), and the inner
products agree by `inducedInnerProduct_conjugate_target`.

## Helper results

- `IsSquareIntegrableInducedForm.of_conjugate_map`: for embeddings with
  `p₂(x) = t p₁(x) t⁻¹`, `v ↦ v(t⁻¹ ·)` maps square integrable induced forms for `p₁` to those for
  `p₂`. This is the argument of the corresponding step in the module
  `Langlands.Global.AdelicStandardWavePacketTransport`, for an arbitrary conjugating point: write
  `t⁻¹ = p₁(u₀ m₀) k₀`, move the unipotent factor to the left, and use that right translation by
  `m₀` on `M(F)A_M \ M(𝔸)` and left translation by `k₀` on `K` preserve the measures.
- `IsIwasawaCompatibleMeasure.of_conjugate_target`: if `μ` is right invariant and compatible
  for `p''` then `δ(m₀)⁻¹ μ` is compatible for `p'`. Proof: `∫_G f = ∫_G f(t⁻¹ ·)`. Conjugation by
  `t` carries the normalized Haar measure of `U'(𝔸)` to that of `t U'(𝔸) t⁻¹`
  (`AdelicSubgroupPoints.exists_adelicSubgroupIso_of_eq_comap`). The latter is right invariant
  (`isMulRightInvariant_normalizedHaarMeasure_range`: `U'(F) \ U'(𝔸)` is compact). Then
  substitute `m ↦ m m₀⁻¹` in `M'(𝔸)` and `k ↦ k₀ k` in `K`.
- `inducedInnerProduct_conjugate_target`: the same substitutions in the inner product. Right
  translation by `m₀` on `M'(F) \ M'(𝔸)` preserves the quotient measure
  (`LeftCosetSpace.measurePreserving_rightTranslate_discrete`, as `rightTranslateMeasurableEquiv`).
  The weight coordinates and the modulus weight `δ(m)⁻¹ = m^{-2ρ}` of the kernel are
  multiplicative in `m`: `y(m m₀) = y(m) + y(m₀)` (`parameterCoordinates_characterLog_mul`) and
  `δ(m m₀)⁻¹ = δ(m)⁻¹ δ(m₀)⁻¹`. Hence the unscaled kernel for the translated forms
  `φ(t ·)`, `ψ(t ·)` with the shifted weight at `(k, m)` equals `δ(m₀)` times the kernel for `p''`
  at `(k₀ k, m m₀)` (`hkernel` in the proof). Scaling the Levi measure by `δ(m₀)⁻¹` cancels this
  factor `δ(m₀)`, and left translation by `k₀` on `K` removes `k₀`.
- `IsWeylConjugation.of_conjugate_target`, `IsWeylConjugation.conjugate_target`,
  `norm_parameterPower_imaginaryParameter`, `parameterPower_mul_parameterPower_inv`,
  `map_conjugate_target`, `monoidHom_map_comp_of_conjugate_map`,
  `parabolicQuotientSubgroup_of_conjugate_map`.

The right invariance of the given Haar measure on `M'(𝔸)` comes from the unimodularity of the
connected reductive group `M'` (`adelicHaarUnimodularity`), which `r'` provides.

## Provenance

Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series* (2011), §2
(p. 311) and §8 (p. 328), works with standard parabolic subgroups; this module supplies the
transport needed to pass to a rationally conjugate target. The Eisenstein series is the defining
sum of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §2.2, (2.1)
(p. 191). The scalar by which it changes under rational conjugation of the parabolic subgroup is
the Library theorem `IsIwasawaCompact.eisensteinSeries_conjugate_parabolic`, derived by
reindexing the rational cosets of that sum and comparing the heights for the same `K`. The
compatibility of Haar measures with the Iwasawa decomposition, with modulus weight `m^{-2ρ}`, is
that of Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.1.13. The
transported coefficients, the shifted weight, the rescaled Levi measure and the cancellations in
both integrals are derived from these definitions.
