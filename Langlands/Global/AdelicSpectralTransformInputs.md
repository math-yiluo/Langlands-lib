# Inputs of the unitary spectral transform

Module `Langlands.Global.AdelicSpectralTransformInputs` defines two auxiliary
notions and states five propositions (`def … : Prop`). It proves nothing and
asserts none of the five: they are the premises of
`Langlands.Global.SpectralTransformReductionStatement` (module
`Langlands.Global.AdelicSpectralTransformReduction`), which proves that together
they imply the published `Langlands.Global.SpectralTransformStatement` (module
`Langlands.Global.AdelicSpectralTransformStatement`; Arthur 2005, Theorem 7.2 (b);
Getz–Hahn (10.22)–(10.24)).

The data of every proposition are those of `SpectralTransformStatement`, with the
same names, binder order and hypotheses (see the Markdown of that module and of
`Langlands.Global.AdelicSpectralTransformSpaces` for `inducedHilbertSpace`,
`spectralFamilySpace`, `symmetricFamilySpace`, `IsSmoothCompactFamily`,
`IsImaginaryIntertwiningOperator`, `spectralMeasure`, `imaginaryParameter`). In
particular `P i` is locally of finite type as a closed subgroup of `G`, supplied
by `haveI` exactly as in the target, `nP i = ∑ i', |T i i'|`, and `μG` is the
quotient of Mathlib's Haar measure on `G(𝔸)` by counting measure on `G(F)`
(`LeftCosetSpace.discreteQuotientMeasure`).

## Sources

- J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4 (2005),
  registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`.
  p.34 (PDF page 46): the intertwining properties
  `E(x, I_P(λ, y)φ, λ) = E(xy, φ, λ)` and
  `M(s, λ) I_P(λ, y) = I_{P'}(sλ, y) M(s, λ)`. Theorem 7.2, p.35 (PDF page 47):
  (a) analytic continuation of `E(x, φ, λ)` and `M(s, λ)φ`, analyticity on
  `i𝔞_P^*` and unitarity of `M(s, λ)` there; (b) the space `L̂_𝒫` and the map
  defined on smooth compactly supported families. After the theorem, p.35: the
  map intertwines `R_𝒫` with `(R̂_𝒫(y)F)_P(λ) = I_P(λ, y) F_P(λ)`.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page =
  printed page + 9). §3, p.314: Theorem 2, the map
  `(F_P) ↦ ∑_P |𝒫(M_P)|⁻¹ Θ_{P, F_P}` on families with `F_P ∈ 𝒲_P` extends to an
  isometry into `L²(G(F) \ G(𝔸))`. Proposition 6, p.329: `E_P(·, φ, λ)` is
  holomorphic on `i𝔞_P^*` for `φ ∈ A^2_P`.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, Theorem 2.3 (1):
  meromorphic continuation of Eisenstein series.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`,
  IV.1.11 (b) (p.141) and VI.2.1 (i) (p.260): holomorphy and unitarity of
  `M(w, λ)` on the unitary axis.
- P. Delorme, *On the spectral theorem of Langlands*, arXiv:2006.12893 (2023
  version), registered as `delorme-2023-spectral-theorem-langlands`, §6
  (PDF page 22): Theorem 6.1 (Lapid's Theorem 2, in the form used here) and the
  Lemma after it, whose proof symmetrizes a family over `W(P|Q)` by
  `F_Q(λ) = ∑_s M(s, s⁻¹λ) ψ(s⁻¹λ)` to obtain a family in `L'`.

## Auxiliary definitions

- `IsEisensteinContinuation hK r hA hT v E D` (for one presented parabolic
  `P`, `v : Fin k → (G(𝔸) → ℂ)`, `E : Fin k → X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)`,
  `D ⊆ X^*(P) ⊗ ℂ`) is the conjunction of
  1. `Set.range (imaginaryParameter F P) ⊆ D`, that is `i(X^*(P) ⊗ ℝ) ⊆ D`;
  2. for all `j`, `g`, `λ ↦ E j λ g` is meromorphic in coordinates with domain
     of holomorphy `D` (`IsMeromorphicInCoordinatesOn`);
  3. for each `j` there is `R : ℝ` with `E j λ = hK.eisensteinSeries (v j) λ`
     whenever `r.IsRegularParameter hA hT R λ`.

  These are, for each `i`, exactly the three conditions that
  `SpectralTransformStatement` imposes on its continuations `E i j` with domain
  `D i`; the reduction uses this to match the two.
- `wavePacketSum e nP c E : G(F) \ G(𝔸) → ℂ` is
  `y ↦ ∑ i, (nP i)⁻¹ * ∫ x, ∑ j, c i j x * E i j (imaginaryParameter F (P i) (e i x)) y.out ∂(spectralMeasure (n i))`,
  evaluated at the chosen representative `y.out` of each coset. This is the
  function of the formula clause of `SpectralTransformStatement`, written as a
  function on the quotient.

## The five propositions

Each is universally quantified over all data of `SpectralTransformStatement`
(S1 over the data of two parabolics, S3' over the data of one).

- S1 `ImaginaryIntertwiningExistenceStatement`. For two presented parabolics
  `P = MU`, `P' = M'U'` of a connected reductive `G` (with Levi decompositions
  and projections `π`, `π'`), `K` maximal compact with `P(𝔸)K = P'(𝔸)K = G(𝔸)`,
  compatible Haar measures `μM`, `μM'`, coordinates `e`, `e'`, weights `β`, `β'`
  (continuous, compactly supported, nonnegative, integral `1`), and a Weyl
  conjugation `(w, cw)` (`IsWeylConjugation p l p' l' w cw`) whose coordinate
  change `x ↦ e'⁻¹(realWeylParameter l cw π' (e x))` preserves Lebesgue measure,
  there is `Mop : ℝⁿ → H_P →L[ℂ] H_{P'}` with
  `IsImaginaryIntertwiningOperator hK hK' … w cw μM μM' e e' β β' Mop`.
  Source: Arthur, Theorem 7.2 (a), the unitary extension of `M(s, λ)` for
  `λ ∈ i𝔞_P^*`; Mœglin–Waldspurger IV.1.11 (b), VI.2.1 (i). It is part 1 of
  the target for a single pair; the binder order matches the per-pair data of
  the target.
- S2 `SymmetricFamilyDensityStatement`. For every family `Mop` with
  `IsImaginaryIntertwiningOperator` for all `(i, i', t)`, the closure of the
  span of `{Φ ∈ L̂ | ∃ k v c, IsSmoothCompactFamily … k v c Φ.1}` is all of
  `L̂ = symmetricFamilySpace … T cw π hw Mop`. This is the first item of
  part 2 of the target. Arthur's Theorem 7.2 (b) presupposes it: the map is
  defined on these families and "extends" to `L̂_𝒫`. Delorme's symmetrization
  (§6, proof of the Lemma) is the tool: it sends a smooth compactly supported
  family to one satisfying the symmetry condition.
- S3' `EisensteinImaginaryContinuationStatement`. For one presented parabolic
  `P = MU` of a connected reductive `G` with `iU` a geometric unipotent radical,
  `K` maximal compact with `P(𝔸)K = G(𝔸)`, and `v : Fin k → (G(𝔸) → ℂ)` with
  every `v j ∈ A^2_P` (`IsSquareIntegrableInducedForm`), there are `E` and `D`
  with `IsEisensteinContinuation hK r hA hT v E D`. Source: Bernstein–Lapid,
  Theorem 2.3 (1) (continuation) and Lapid 2011, Proposition 6 (holomorphy on
  `i𝔞_P^*`). In the Library these are `EisensteinMeromorphicContinuationStatement`
  and `EisensteinImaginaryAxisHolomorphyStatement`, stated for one `v`; S3' asks
  for one domain `D` for finitely many `v j`.
- S3 `SymmetricFamilyGramStatement`. For every family `Mop` as in S2, all
  `Φ, Φ' ∈ L̂` with `IsSmoothCompactFamily … k v c Φ.1` and
  `IsSmoothCompactFamily … k' v' c' Φ'.1`, and all `E, D, E', D'` with
  `IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v i) (E i) (D i)` (and
  likewise for `v', E', D'`) for every `i`:
  `MemLp (wavePacketSum e nP c E) 2 μG` and
  `∫ y, conj (wavePacketSum e nP c E y) * wavePacketSum e nP c' E' y ∂μG = ⟪Φ.1, Φ'.1⟫`,
  the inner product of `spectralFamilySpace`. Source: Lapid 2011, Theorem 2
  (Delorme, Theorem 6.1) states that the map is isometric on these families;
  S3 is its polarized form (an isometry of complex inner product spaces
  preserves inner products), in Arthur's normalization `n_P⁻¹`.
- S4 `WavePacketTranslationStatement`. For every family `Mop` as in S2, every
  `Φ ∈ L̂` with `IsSmoothCompactFamily … k v c Φ.1` and continuations `E, D` as
  in S3, every `y ∈ G(𝔸)` and every `ε > 0`, there are `Φ' ∈ L̂`, `k', v', c'`,
  `E', D'` with `IsSmoothCompactFamily … k' v' c' Φ'.1`, continuations as in S3,
  and
  `eLpNorm (fun z => wavePacketSum e nP c E (mk (z.out * y)) - wavePacketSum e nP c' E' z) 2 μG < ENNReal.ofReal ε`.
  That is, the right translate by `y` of the wave packet sum is an `L²` limit of
  wave packet sums of smooth compactly supported families. Source: Arthur
  p.34, `E(x, I_P(λ, y)φ, λ) = E(xy, φ, λ)` and
  `M(s, λ) I_P(λ, y) = I_{P'}(sλ, y) M(s, λ)`, so the translate is the wave
  packet of `R̂_𝒫(y)F ∈ L̂_𝒫` (p.35), approximated through S2 and S3.

## Notes on the formulation

- S3 is stated as a Gram identity between wave packet sums, not as the
  existence of an isometry, so that the reduction can build the isometry
  itself (`LinearMap.extendOfIsometry`).
- S3 and S4 quantify over every choice of continuations satisfying
  `IsEisensteinContinuation`, as the target's formula clause does, so that
  the formula clause of the target follows for every such choice.
- The `ε`-form of S4 avoids stating the action `R̂(y)` on `L̂`, which the
  Library does not define.
