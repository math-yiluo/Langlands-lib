# The wave packet isometry

Module `Langlands.Global.AdelicWavePacketIsometryStatement` states
`Langlands.Global.WavePacketIsometryStatement` as a proposition definition.
It supplies no proof.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9). §3, p.314: the Hilbert space `L` of families
  `F_P : i𝔞_P^* → Ind_{P(𝔸)}^{G(𝔸)} L²_disc(A_M M \ M(𝔸))`, `P ⊇ P₀`, with
  `‖(F_P)‖² = ∑_P |P(M_P)|⁻¹ ‖F_P‖²_*` and
  `F_{P'}(wλ) = M(w, λ)F_P(λ)` for `w ∈ Ω(P, P')`; the dense subspace `L°` of
  families with every `F_P ∈ W_P`; and Theorem 2: the map
  `(F_P) ↦ ∑_P |P(M_P)|⁻¹ Θ_{P, F_P}` on `L°` extends to an isometry from `L`
  to a subspace of `L²(G \ G(𝔸))`.
- J. Arthur, *An introduction to the trace formula*, in: Harmonic Analysis,
  the Trace Formula, and Shimura Varieties, Clay Math. Proc. 4 (2005),
  registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`,
  Theorem 7.2 (b), printed p.35 (PDF page 47): for an associated class `𝒫`,
  the norm `‖F‖² = ∑_{P ∈ 𝒫} n_P⁻¹ ∫_{i𝔞_P^*} ‖F_P(λ)‖² dλ` with
  `n_P = ∑_{P' ∈ 𝒫} |W(𝔞_P, 𝔞_{P'})|`, the symmetry condition
  `F_{P'}(sλ) = M(s, λ)F_P(λ)`, and the map
  `F ↦ ∑_P n_P⁻¹ ∫_{i𝔞_P^*} E(x, F_P(λ), λ) dλ` on smooth compactly
  supported `F_P` with values in a finite-dimensional space, which extends to
  a unitary map onto a closed subspace of `L²(G(F) \ G(𝔸))`.
- J. Getz and H. Hahn, *An introduction to automorphic representations*
  (2024), registered as `getz-hahn-2024-automorphic-representations`, §10.5,
  p.281 (PDF page 293), (10.22)–(10.24): the same families, inner product and
  `n_P`, on `L²([G])` and `i(𝔞_M^G)^*`.

## Statement

The data, for a number field `F : Type`:

- `G` connected reductive and a finite type `I`; for each `i : I` a parabolic
  `p i : P i → G` with geometric unipotent radical `iU i`, Levi `l i`,
  presentation `r i : ParabolicRootPresentation (p i) (l i) (a i)` and Levi
  projection `π i` with `l i ≫ π i = 𝟙`; all groups affine, `M i` locally of
  finite type (`P i` locally of finite type as a closed subgroup, supplied by
  `haveI`);
- `K` maximal compact with `P i(𝔸)K = G(𝔸)` for every `i`, a closed matrix
  embedding `rho`, and the smooth-structure data `hsmooth`, `hcalc`;
- Haar measures `μM i` with
  `IsIwasawaCompatibleMeasure K (hK i).isCompact (p i) (iU i) (l i) (μM i)`;
- coordinates `e i : ℝ^{n i} ≃ X^*(P i) ⊗ ℝ` and continuous compactly
  supported weights `β i` with `∫ β i = 1`, which define
  `(·,·)_{P i} = inducedInnerProduct K (hK i).isCompact (p i) (l i) (μM i) (e i) (β i)`;
- wave packet data as in `WavePacketInnerProductStatement`: `v i j ∈ A^2_{P i}`,
  smooth compactly supported `c i j`, and Eisenstein continuations `E i j`,
  meromorphic with domain `D i ⊇ i𝔞_{P i}^*` and equal to
  `(hK i).eisensteinSeries (v i j)` for `Re λ` sufficiently regular;
- for each pair `(i, i')` a finite type `T i i'` and pairs
  `(w i i' t, cw i i' t)` with `IsWeylConjugation`, such that
  `t ↦ weylParameter (l i) (cw i i' t) (π i')` is a bijection onto
  `weylParameterSet (p i) (l i) (p i') (l i') (π i')`, that is `Ω(P i, P i')`;
- for each `(i, i', t)`, the coordinate change
  `x ↦ (e i')⁻¹ (realWeylParameter (l i) (cw i i' t) (π i') (e i x))`
  preserves Lebesgue measure;
- expansions `M(w i i' t, λ)(v i j) = ∑ q, coeff i i' t j q λ • ψ i i' t j q`
  for `Re λ` sufficiently regular, with `ψ i i' t j q ∈ A^2_{P i'}` and
  coefficients meromorphic with domain `DM i ⊇ i𝔞_{P i}^*`;
- the Weyl compatibility: for all `i, i', t`, `x` and `g`,
  `∑ j', c i' j' (x') · v i' j' g = ∑ j, c i j x · ∑ q, coeff i i' t j q (i e i x) · ψ i i' t j q g`
  with `x' = (e i')⁻¹ (w (e i x))`.

Let `Θ i (g) = ∫ ∑ j, c i j x · E i j (i e i x) g d(spectralMeasure (n i))(x)`,
`n_P i = ∑ i', |T i i'|`, `Φ = ∑ i, (n_P i)⁻¹ Θ i`, and `μG` the quotient of
Mathlib's Haar measure on `G(𝔸)` by counting measure on `G(F)`. The
conclusion: `y ↦ Φ(y.out)` is in `L²(G(F) \ G(𝔸), μG)` and
`∫ ‖Φ(y.out)‖² dμG = ∑ i, (n_P i)⁻¹ · ∫ Re (F i x, F i x)_{P i} d(spectralMeasure (n i))(x)`,
where `F i x = ∑ j, c i j x · v i j`.

## Correspondence with the source

- The families. `F i` is `F_{P i}` written in the coordinates
  `λ = i e i (x)`, with values in the span of the `v i j`, smooth and
  compactly supported: Arthur's smooth compactly supported `F_P` with values
  in a finite-dimensional space, and Lapid's `F_P ∈ W_P`. The data, measures,
  enumeration of `Ω(P i, P i')`, Eisenstein continuations and intertwining
  expansions follow `WavePacketInnerProductStatement` (see its Markdown).
- The symmetry condition. `F_{P'}(wλ) = M(w, λ)F_P(λ)` for
  `w ∈ Ω(P, P')` becomes the Weyl compatibility: its left side is
  `F i' (x')` at `w(i e i x) = i e i' (x')`, and its right side is
  `M(w, λ)` applied to `F i x = ∑ j, c i j x · v i j`, using the expansion
  of each `M(w, λ)(v i j)`, holomorphic on `i𝔞_{P i}^*`. The identity is
  required at every `g`, which for automorphic forms is the same as almost
  everywhere.
- The weights. `n_P i = ∑ i', |Ω(P i, P i')|` is Arthur's and Getz–Hahn's
  `n_P` (10.23) when the family is an associated class of standard
  parabolics. The statement allows any finite family: `|Ω(P, P')| = 0` unless
  `P` and `P'` are associate, and within the members of the family associate
  to a given `P'`, `|Ω(P, P')| = |Ω(P', P')|` and `n_P` is constant, so
  `∑_P n_P⁻¹ |Ω(P, P')| = 1`. Expanding `‖Φ‖²` by formula (4) of Lapid's
  Proposition 2 and the symmetry condition gives the identity for every
  finite family; in particular for the family of all standard parabolics.
  There `n_P = |P(M_P)|`, Lapid's weight, the number of parabolic subgroups
  with Levi component `M_P`: each of them is `w⁻¹ P' w` for exactly one
  standard `P'` and one `s ∈ Ω(P, P')` represented by `w`. This is
  explanatory and not proved here.
- Measures. Arthur and Lapid take the measures on the spaces `𝔞_P` induced
  from one Weyl-invariant measure on `𝔞_0`, so every `s ∈ Ω(P, P')`
  preserves them. Here the measure on `𝔞_{P i}` is Lebesgue measure in the
  coordinates dual to `e i`, and the hypothesis that the coordinate changes
  preserve Lebesgue measure expresses the same invariance; for `i = i'` it
  holds automatically, since `Ω(P, P)` is a finite group. Some such
  hypothesis is necessary: replacing `e i` by `e i ∘ S` (and `c i j` by
  `c i j ∘ S`, the same `F_{P i}` as a function of `λ`) multiplies `Θ i` by
  `|det S|⁻¹` and `∫ (F i, F i)_{P i} dλ` by `|det S|⁻²`. So `‖Θ i‖²` and the
  `i`-th term on the right scale by `|det S|⁻²`, but the cross terms
  `(Θ i, Θ i')` of `‖Φ‖²` scale by `|det S|⁻¹`: the identity is not invariant
  under rescaling one `e i` alone.
  `K`, `μM i`, `dg`, the regions and the universe are as in
  `WavePacketInnerProductStatement`. This is explanatory.
- `L²(G \ G(𝔸))`. As in Lapid and Arthur, the space is
  `L²(G(F) \ G(𝔸))` and the parameters range over `i𝔞_P^*`; Getz–Hahn
  divide by `A_G` and use `i(𝔞_M^G)^*`.

## Scope

The statement is the isometry on the dense subspace `L°` of smooth
compactly supported families (as a norm identity; the inner-product identity
follows by polarization since `Φ` is linear in the family). The Hilbert space
`L`, the density of `L°` in it, and the extension of the map to `L` (formal
for a linear isometry on a dense subspace) are not stated. Surjectivity
onto `L²` (Langlands; Arthur Theorem 7.2 (b), (7.5); Getz–Hahn
Theorem 10.5.1) is not part of this statement.
