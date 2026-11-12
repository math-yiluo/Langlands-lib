# The unitary spectral transform

Module `Langlands.Global.AdelicSpectralTransformStatement` states
`Langlands.Global.SpectralTransformStatement` as a proposition definition.
It supplies no proof. The spaces it uses are defined in
`Langlands.Global.AdelicSpectralTransformSpaces` (see its Markdown).

## Sources

- J. Arthur, *An introduction to the trace formula*, in: Harmonic Analysis,
  the Trace Formula, and Shimura Varieties, Clay Math. Proc. 4 (2005),
  registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`,
  Theorem 7.2, printed p.35 (PDF page 47). (a): for `λ ∈ i𝔞_P^*`, `M(s, λ)`
  is analytic and extends to a unitary operator from `H_P` to `H_{P'}`.
  (b): for an associated class `𝒫`, let `L̂_𝒫` be the Hilbert space of
  families of measurable functions `F_P : i𝔞_P^* → H_P`, `P ∈ 𝒫`, with
  `F_{P'}(sλ) = M(s, λ)F_P(λ)` for `s ∈ W(𝔞_P, 𝔞_{P'})` and
  `‖F‖² = ∑_P n_P⁻¹ ∫_{i𝔞_P^*} ‖F_P(λ)‖² dλ < ∞`,
  `n_P = ∑_{P' ∈ 𝒫} |W(𝔞_P, 𝔞_{P'})|`. "Then the mapping that sends `F` to
  the function `∑_P n_P⁻¹ ∫_{i𝔞_P^*} E(x, F_P(λ), λ) dλ`, defined whenever
  `F_P(λ)` is a smooth, compactly supported function of `λ` with values in a
  finite dimensional subspace of `H_P^0`, extends to a unitary mapping from
  `L̂_𝒫` onto a closed `G(𝔸)`-invariant subspace `L²_𝒫(G(F) \ G(𝔸))` of
  `L²(G(F) \ G(𝔸))`." `H_P`, `H_P^0`, the measures and `M(s, λ)` are defined
  on pp.32–34 (PDF pages 44–46).
- J. Getz and H. Hahn, *An introduction to automorphic representations*
  (2024), registered as `getz-hahn-2024-automorphic-representations`, §10.5,
  pp.281–282 (PDF pages 293–294): the same families (10.22), inner product,
  `n_P` (10.23) and integral (10.24) on `[G] = A_G G(F) \ G(𝔸)` with
  parameters in `i(𝔞_M^G)^*`, and Theorem 10.5.1, citing Arthur's
  Theorem 7.2.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §2, p.312
  (PDF page 321): `M(w, λ)`, `λ ∈ i𝔞_P^*`, extends to a unitary operator on
  `Ind_{P(𝔸)}^{G(𝔸)} L²_disc(A_M M(F) \ M(𝔸))`; §3, p.314 (PDF page 323):
  the Hilbert space `L` of families, its dense subspace `L°` of families
  with `F_P ∈ W_P`, and Theorem 2: the map `(F_P) ↦ ∑_P |P(M_P)|⁻¹ Θ_{P,F_P}`
  on `L°` extends to an isometry from `L` to `L²(G(F) \ G(𝔸))`.
- P. Delorme, *On the spectral theorem of Langlands*, arXiv:2006.12893
  (2023 version), registered as `delorme-2023-spectral-theorem-langlands`,
  Theorem 6.1 and Lemma 6.2 (PDF page 22): Lapid's Theorem 2 and the
  symmetrization of wave packets over `W(P|Q)`.

## Statement

The data, for a number field `F : Type`:

- `G` connected reductive and a finite type `I`; for each `i : I` a
  parabolic `p i : P i → G` with geometric unipotent radical `iU i`, Levi
  `l i`, Levi decomposition `M i ⋉ U i ≅ P i`
  (`IsIso (subgroupMultiplication (l i) (iU i))`), presentation
  `r i : ParabolicRootPresentation (p i) (l i) (a i)` and Levi projection
  `π i` with `l i ≫ π i = 𝟙`; all groups affine, `M i` locally of finite
  type (`P i` locally of finite type as a closed subgroup, supplied by
  `haveI`), `p i` and `iU i ≫ p i` closed immersions;
- `K` maximal compact with `P i(𝔸)K = G(𝔸)` for every `i`, a closed matrix
  embedding `rho`, and the smooth-structure data `hsmooth`, `hcalc`;
- Haar measures `μM i` with
  `IsIwasawaCompatibleMeasure K (hK i).isCompact (p i) (iU i) (l i) (μM i)`;
- coordinates `e i : ℝ^{n i} ≃ X^*(P i) ⊗ ℝ` and continuous compactly
  supported weights `β i ≥ 0` with `∫ β i = 1`, which define
  `H_{P i} = inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i) (e i) (β i)`;
- for each pair `(i, i')` a finite type `T i i'` and pairs
  `(w i i' t, cw i i' t)` with `IsWeylConjugation`, such that
  `t ↦ weylParameter (l i) (cw i i' t) (π i')` is a bijection onto
  `weylParameterSet (p i) (l i) (p i') (l i') (π i')`, that is
  `Ω(P i, P i')`;
- `hw`: for each `(i, i', t)`, the coordinate change
  `x ↦ (e i')⁻¹ (realWeylParameter (l i) (cw i i' t) (π i') (e i x))`
  preserves Lebesgue measure.

Let `nP i = ∑ i', |T i i'|` and `μG` the quotient of Mathlib's Haar measure
on `G(𝔸)` by counting measure on `G(F)`. The conclusion has two parts.

1. There are operators `Mop i i' t x : H_{P i} →L[ℂ] H_{P i'}` with
   `IsImaginaryIntertwiningOperator … (w i i' t) (cw i i' t) … (Mop i i' t)`
   for all `i, i', t`; that is, `Mop i i' t x = M(w i i' t, i e_i(x))`.
2. For every such family `Mop`, there is a linear isometry
   `Ē : L̂ →ₗᵢ[ℂ] L²(G(F) \ G(𝔸), μG)`, where
   `L̂ = symmetricFamilySpace … T cw π hw Mop` carries the norm
   `‖Φ‖² = ∑ i, (nP i)⁻¹ ∫ ‖Φ_i(x)‖² d(spectralMeasure (n i))(x)`, such that
   - the span of the `Φ ∈ L̂` that are smooth compactly supported families
     (`IsSmoothCompactFamily`) is dense in `L̂`;
   - for every such `Φ`, with `Φ_i(x)` the class of the restriction of
     `∑ j, c i j x • v i j`, and every choice of Eisenstein continuations
     `E i j`, meromorphic with domain `D i ⊇ i(X^*(P i) ⊗ ℝ)` and equal to
     `(hK i).eisensteinSeries (v i j)` for `Re λ` sufficiently regular,
     `Ē Φ` is almost everywhere the function
     `y ↦ ∑ i, (nP i)⁻¹ ∫ ∑ j, c i j x · E i j (i e_i(x)) (y.out) d(spectralMeasure (n i))(x)`;
   - the range of `Ē` is closed;
   - the range of `Ē` is invariant under right translation by `G(𝔸)`: for
     `f` in the range and `y ∈ G(𝔸)`, some `f'` in the range is almost
     everywhere `x ↦ f(x y)`.

## Correspondence with the source

- The operators `M(s, λ)`. The Library has `M(w, λ)` only as the convergent
  integral for `Re λ` sufficiently regular. Part 1 is the part of Arthur's
  Theorem 7.2 (a) used in (b): the operators on the imaginary axis exist,
  characterized by `IsImaginaryIntertwiningOperator` through the
  meromorphic continuation of `M(w, λ)` on `A^2_{P i}`. They are unique,
  since the restrictions of `A^2_{P i}` are dense in `H_{P i}` (Markdown of
  the spaces module), so part 2, which quantifies over all such `Mop`, is a
  statement about Arthur's operators; part 1 keeps part 2 from being
  vacuous. Unitarity of `M(w, λ)` is the accepted
  `IntertwiningImaginaryUnitarityStatement` (with `e' = w ∘ e`; under `hw`
  the inner products for `e i'` and for `w ∘ e i` agree, since replacing
  `e'` by `e' ∘ T` multiplies `(·,·)_{P'}` by `|det T|⁻¹`) and is not
  repeated here.
- The space `L̂`. Arthur's families of measurable functions with finite
  norm are the elements of `spectralFamilySpace`, in the coordinates
  `λ = i e_i(x)`, with `dλ` the measure `spectralMeasure (n i)` dual to the
  measure on `𝔞_{P i}` for which `∫ β i = 1`; the symmetry condition, almost
  everywhere, cuts out `symmetricFamilySpace`. `H_{P i}` is Arthur's `H_P`
  in Iwasawa coordinates (Markdown of the spaces module).
- The map. Arthur's map is defined on the smooth compactly supported `F_P`
  with values in a finite-dimensional subspace of `H_P^0`, the
  `IsSmoothCompactFamily` elements of `L̂`, by
  `∑_P n_P⁻¹ ∫ E(x, F_P(λ), λ) dλ`. For `F_P(λ) = ∑ j, c_j(λ) v_j`,
  `E(x, F_P(λ), λ) = ∑ j, c_j(λ) E(v_j, λ)(x)`, where the Library's
  `eisensteinSeries` follows Lapid's normalization (`v_j ∈ A^2_P`, with
  `e^{ρ_P(H_P)}` inside `v_j`; Arthur puts it into the series), and the
  continuation to `i𝔞_P^*` enters, as in `WavePacketInnerProductStatement`
  and `WavePacketIsometryStatement`, through every meromorphic `E i j` that
  agrees with the convergent series for `Re λ` sufficiently regular and is
  holomorphic on a domain containing `i𝔞_{P i}^*` (Lapid's Proposition 6 is
  `EisensteinImaginaryAxisHolomorphyStatement`). The function is read at
  representatives `y.out`; the continuations are left `G(F)`-invariant on
  `D i` (for fixed `g` and `γ ∈ G(F)`, `E i j λ (γg) - E i j λ g` is
  meromorphic on `D i` and vanishes for `Re λ` sufficiently regular), so
  this is a function on `G(F) \ G(𝔸)`.
- "Extends to a unitary mapping onto a closed `G(𝔸)`-invariant subspace".
  `Ē` is a linear isometry, hence unitary onto its range; it agrees with
  Arthur's map on the smooth compactly supported families, which are dense,
  so it is the extension. Its range, Arthur's `L²_𝒫(G(F) \ G(𝔸))`, is
  closed and invariant under the right regular representation; the
  invariance is stated through representatives, since right translation by
  `y` preserves `μG` (`G(𝔸)` is unimodular) and so acts on classes.
- The family. Arthur takes an associated class `𝒫` of standard parabolics;
  here `(P i)_{i ∈ I}` is any finite family, as in
  `WavePacketIsometryStatement`, and `nP i = ∑ i', |Ω(P i, P i')|` is
  Arthur's `n_P` for an associated class. `Ω(P i, P i')` is empty unless
  `P i` and `P i'` are associate, so `L̂` is the orthogonal sum of the
  spaces of the association classes met by the family, and within each the
  weights satisfy `∑_P n_P⁻¹ |Ω(P, P')| = 1`, the identity behind the
  isometry (Markdown of `WavePacketIsometryStatement`). The density of the
  smooth compactly supported families in `L̂`, implicit in Arthur's
  "extends", follows by symmetrizing such families over the `Ω(P i, P i')`
  (Delorme's Lemma 6.2): the symmetrization is the orthogonal projection
  onto `L̂`, and it preserves smooth compact support because
  `M(w, λ)(∑ j, c_j(λ) v_j)` is again of this form on `i𝔞_P^*`. This is
  explanatory and not proved here.
- Measures. As in `WavePacketIsometryStatement`: `dg` is Mathlib's Haar
  measure on `G(𝔸)`, `dk` the probability measure on `K`, `du` the measure
  with `vol(U(F) \ U(𝔸)) = 1`, `μM i` the compatible measure, `𝔞_{P i}`
  carries Lebesgue measure in the coordinates dual to `e i`, and `dλ` is its
  dual. These are Arthur's compatibility conditions (p.32). The hypothesis
  `hw` expresses the Weyl invariance of the measures, automatic in Arthur's
  setting and necessary here (rescaling one `e i` alone changes the cross
  terms of the norm identity differently from the diagonal ones).
- The compact subgroup and parabolics. Arthur fixes `K` and standard
  parabolics in good position; here `K` is any maximal compact subgroup with
  `P i(𝔸)K = G(𝔸)`, as in the published wave-packet statements (Markdown of
  `WavePacketInnerProductStatement`).
- `G(F) \ G(𝔸)`. As Arthur and Lapid, the statement is on
  `L²(G(F) \ G(𝔸))` with parameters in `i𝔞_P^*`; Getz–Hahn state the same
  theorem on `L²([G])` with `i(𝔞_M^G)^*`.

## Scope

The statement does not identify the range of `Ē` with Getz–Hahn's
`L²_𝒫([G])` and does not state the orthogonal decomposition (7.5); the
decomposition on `[G]` is `SpectralDecompositionStatement` (module
`Langlands.Global.AdelicSpectralDecompositionStatement`). It does not state
that `Ē` intertwines the right regular representation with
`R_𝒫(y)F(λ) = I_P(λ, y)F_P(λ)` (only invariance of the range), nor the
unitarity or functional equations of the operators `Mop`. That `L̂` is
closed in `spectralFamilySpace` is not stated.
