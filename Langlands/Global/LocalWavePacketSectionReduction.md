# Lapid's Proposition 2 for holomorphic families of inducing vectors, and the change of `K`

Module `Langlands.Global.LocalWavePacketSectionReduction` states three
propositions and proves one implication:

- `Langlands.Global.LocalWavePacketSectionTruncationCompactStatement`: Lapid's
  Proposition 2, formula (4), for wave packets whose inducing vectors are
  holomorphic families `λ ↦ ∑_i b_i(λ) v_i` with entire coefficients `b_i`,
  for one compact subgroup `K` with the properties that
  `ArthurTruncation.TruncationOrthogonalProjectionStatement` asserts for some
  compact subgroup;
- `Langlands.Global.TruncatedWavePacketSectionLimitStatement`: the sufficient
  condition with which Lapid begins the proof of Proposition 2 (§8), for the
  same data;
- `Langlands.Global.localWavePacketSectionTruncationCompact_of_sectionLimit`
  (theorem): the second statement implies the first;
- `Langlands.Global.LocalWavePacketCompactChangeStatement`: the implication
  `TruncationOrthogonalProjectionStatement.{0} →
  LocalWavePacketSectionTruncationCompactStatement →
  LocalWavePacketInnerProductStatement`.

The module proves neither of the first two statements and does not prove
`LocalWavePacketCompactChangeStatement`; it is a proposition whose truth is
explained below.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9).
  - §2, p.311: one maximal compact `K` "in good position with respect to
    `M₀`", `A^2_P`, `φ_λ(g) = φ(g) e^{⟨λ, H_P(g)⟩}`, the Eisenstein series;
    p.312: the intertwining operators, the Working hypothesis and its
    consequence that `M(w, λ)` is unitary, hence holomorphic, for
    `λ ∈ i𝔞_P^*`, and the truncation operator `Λ^T`.
  - §3, p.314: "denote by `W_P` the space of compactly supported smooth
    functions on `i𝔞_P^*` taking values in a finite-dimensional subspace of
    `A^2_P` such that `E_P(·, φ(λ), λ)` is smooth on `i𝔞_P^*`. (Ultimately,
    the last condition is redundant.)", `Θ_{P,φ}(g) = ∫ E_P(g, φ(λ), λ) dλ`,
    Proposition 2 and formula (4):
    `(Θ_{P,φ}, Θ_{P',φ'}) = ∫ ∑_{w ∈ Ω(P,P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`.
  - Lemma 9 and its proof, p.327, and §8, p.328, first paragraph: "By Lemma 9
    it suffices to show that the inner product
    `(Λ^T Θ_{P,φ}, Λ^T Θ_{P',φ'})_{G\G(𝔸)}` converges to the right-hand side
    of (4) as `T → ∞` in `C`."
  - Proposition 6, p.329: for every `φ ∈ A^2_P` the Eisenstein series
    `E_P(·, φ, λ)` is holomorphic for `λ ∈ i𝔞_P^*`; Lapid deduces it from
    Proposition 2 (§8, pp.328–330).
- J. Arthur, *An introduction to the trace formula* (2005), in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §4, p.24, a
  suitable maximal compact `K` with `G(𝔸) = P₀(𝔸)K`; §13, Proposition 13.1 and
  the paragraph after its proof, pp. 68–69: `Λ^T` extends to an orthogonal
  projection on `L²`.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §2.2: the twist
  `φ_λ` defined with the Iwasawa height of the chosen compact subgroup.
- A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965),
  registered as `borel-tits-1965-groupes-reductifs`, Théorème 4.13: minimal parabolic subgroups over `F` are conjugate by a
  rational point (in the Library, `GroupScheme.minimalParabolicConjugacy`).

## Holomorphic families of inducing vectors

The data of `LocalWavePacketSectionTruncationCompactStatement` are those of
`LocalWavePacketInnerProductStatement` (module
`Langlands.Global.AdelicLocalWavePacketStatement`), with the fixed inducing
vectors replaced by families:

| Lapid | Lean |
|---|---|
| `φ(λ) = ∑_j c_j(λ) φ_j(λ)` with `φ_j(λ) = ∑_i b_{j,i}(λ) v_{j,i}` | `v : Fin k → Fin q → G(𝔸) → ℂ` with every `v j i` in `A^2_P` (`IsSquareIntegrableInducedForm K …`), `b : Fin k → Fin q → X^*(P) ⊗ ℂ → ℂ` with `IsMeromorphicInCoordinatesOn (b j i) Set.univ`, and smooth compactly supported `c j` on `ℝⁿ` |
| `E_P(·, φ_j(λ), λ)` (continuation) | `E j`, with `λ ↦ E j λ g` meromorphic with domain of holomorphy `D`, `i e(S) ⊆ D`, and `E j λ g = ∑_i b j i λ · E_{P,K}(v j i, λ)(g)` for `r`-regular `λ` (`hK.eisensteinSeries`) |
| `M(w, λ)φ_j(λ)` | `∑_i b j i λ · M(w_t, λ)(v j i)(g) = ∑_l coeff t j l λ · ψ t j l g` for `r`-regular `λ` (`hK.intertwiningOperator`), with `ψ t j l ∈ A^2_{P'}` and `coeff t j l` meromorphic with domain `DM ⊇ i e(S)` |
| `φ'(μ)` for `P'` | `v'`, `b'`, `c'`, `E'`, `D'` in the same way |

`IsMeromorphicInCoordinatesOn f D` includes that `D` is open and dense and
that `f` is holomorphic on `D`; for `D = Set.univ` it says that `b j i` is an
entire function of `λ ∈ X^*(P) ⊗ ℂ`. The packets are, as in
`LocalWavePacketInnerProductStatement`,
`Θ(g) = ∫ ∑_j c_j(x) E_j(i e(x))(g) dx` and
`Θ'(g) = ∫ ∑_j c'_j(x) E'_j(i e'(x))(g) dx` for `spectralMeasure`.

The conclusion is `Θ, Θ' ∈ L²(G(F) \ G(𝔸))` and

`(Θ, Θ') = ∫ ∑_t ∑_{j,l} ∑_{j',i'} c_j(x) coeff_{t,j,l}(λ)
conj(c'_{j'}(x'_t)) conj(b'_{j',i'}(w_t λ)) (ψ_{t,j,l}, v'_{j',i'})_{P'} dx`,

with `λ = i e(x)` (`imaginaryParameter F P (e x)`),
`w_t λ = weylParameter l (cw t) π' λ`, and
`x'_t = e'⁻¹(realWeylParameter l (cw t) π' (e x))` the coordinates of
`w_t λ / i`. This is (4): `M(w, λ)φ(λ) = ∑_j c_j(x) ∑_l coeff_{t,j,l}(λ) ψ_{t,j,l}`
and `φ'(wλ) = ∑_{j'} c'_{j'}(x'_t) ∑_{i'} b'_{j',i'}(wλ) v'_{j',i'}`, and
`(·,·)_{P'} = inducedInnerProduct K … μM' e' β'` is conjugate linear in its
second entry. The normalizations (`spectralMeasure`, `μM'`, `e'`, `β'`, the
measure `μG`) are those of `LocalWavePacketInnerProductStatement`.

### Comparison with Lapid's `W_P`

Lapid only asks that `E_P(·, φ(λ), λ)` be smooth on `i𝔞_P^*`; his
definition of `W_P` asks nothing of the Eisenstein series of the individual
vectors of the finite-dimensional subspace (he remarks that the condition is
ultimately redundant: by Proposition 6, which he deduces after Proposition 2,
every such series is holomorphic on `i𝔞_P^*`). The statement has the same
feature: only the combinations `E j` are assumed holomorphic near the support,
not the series `E_{P,K}(v j i, ·)`. Two differences remain. The coefficients `b j i` are
entire functions of `λ`, not smooth functions on `i𝔞_P^*`, because `E j` is
tied to the convergent series on the regular region; the smooth dependence on
`x` is carried by `c j`. And, as in `LocalWavePacketInnerProductStatement`,
only a neighbourhood of the support is required to lie in the domain of
holomorphy (local regularity), not all of `i𝔞_P^*`.

For `q = 1` and `b = 1` the data are those of
`LocalWavePacketInnerProductTruncationCompactStatement` (module
`Langlands.Global.LocalWavePacketTruncationReduction`), and the hypotheses on
`K` are those listed below, which include the norm-one projection in
addition to the full-quotient one.

## The compact subgroup `K`

Besides `P(𝔸)K = P'(𝔸)K = G(𝔸)` and maximality, the statement assumes, for
the minimal parabolic `P₀` of `r` (the standard minimal parabolic of the
maximal split torus `r.data.i` and the generic cocharacter `r.data.ν`), and
for reflection data `D₀` and the character comparison `hρ₀`:

- `P₀(𝔸)K = G(𝔸)`
  (`IsIwasawaCompact (Standard.parabolicHom r.data.i r.data.ν ∅) K`);
- for every Siegel setup `(T₀, j)`, `P₀(𝔸) ∩ K` commutes with the positive
  torus (`AdelicSiegelFactors.IsPositiveTorusCompatible`);
- for some `C` and every truncation parameter `T` with `β(T) > C` for every
  simple root `β`, both the norm-one truncation
  `normOneTruncation hG r.isCompatible.maximalSplit D₀ hK₀ hρ₀ T` on
  `G(F) \ G(𝔸)¹` and the full-quotient truncation
  `truncation hG r.isCompatible.maximalSplit D₀ hK₀ hρ₀ T` on `G(F) \ G(𝔸)`
  satisfy `IsOrthogonalL2Extension` for `normOneRationalQuotientHaarMeasure F G`
  and `rationalQuotientHaarMeasure F G`.

These are the properties that `TruncationOrthogonalProjectionStatement`
asserts for one compact subgroup, for every `D` and `hρ`. A maximal compact
subgroup in Lapid's good position satisfies them when Arthur's Proposition
13.1 holds for it; the class they define is wider (see the `SL₂` example in
the Markdown of `LocalWavePacketTruncationReduction`).

## `TruncatedWavePacketSectionLimitStatement`

The data and hypotheses of `LocalWavePacketSectionTruncationCompactStatement`,
and any direction `v₀` on which every simple root of
`(r.data.i, r.data.ν)` is positive; the statement quantifies over all such
`v₀`. With `f(y) = Θ(y.out)`, `f'(y) = Θ'(y.out)` on `G(F) \ G(𝔸)` and
`trunc j` the full-quotient truncation with respect to `K` at the parameter
`j • v₀`, the conclusion is:

1. `f` and `f'` are measurable and bounded on every compact set;
2. for all large `j`, `trunc j f` and `trunc j f'` are in `L²(μG)`;
3. the real parts of `∫ trunc j f · conj (trunc j f) dμG` and of the same
   integral for `f'` are bounded above for all large `j`;
4. `∫ trunc j f · conj (trunc j f') dμG` tends to the right side of (4)
   written above as `j → ∞`.

Item 4 is Lapid's convergence along the ray `j • v₀`; items 1–3 are used by
Lapid without comment. Item 3 is listed because the data contain the
expansions of `M(w, λ)` only for `Ω(P, P')`. The correspondence is that of
`TruncatedWavePacketLimitStatement`, explained in the Markdown of
`LocalWavePacketTruncationReduction`.

## The theorem `localWavePacketSectionTruncationCompact_of_sectionLimit`

Take the data and hypotheses of
`LocalWavePacketSectionTruncationCompactStatement`. The proof applies
`TruncatedWavePacketSectionLimitStatement` with the direction
`v₀ = 1 ⊗ r.data.ν`, on which every simple root is positive
(`cocharacter_simple_pos`), and obtains items 1–4. It keeps the
full-quotient half of the projection hypothesis. Then
`ArthurTruncation.fullQuotientTruncationPairing`, with
`ArthurTruncation.truncationFiniteness`, `r.isCompatible.maximalSplit` and
`r.isCompatible.generic`, turns items 1–4 into `MemLp f 2 μG`,
`MemLp f' 2 μG` and `∫ f · conj f' dμG = ` the right side of (4). The measure
`μG` of the conclusion is `rationalQuotientHaarMeasure F G` by definition.

## `LocalWavePacketCompactChangeStatement`

`LocalWavePacketInnerProductStatement` is stated for every maximal compact
`K` with `P(𝔸)K = P'(𝔸)K = G(𝔸)`, a class on which no truncation operator
is available (the minimal parabolic need not have Iwasawa coverage). Arthur's
projection statement gives one compact subgroup `K₀` with the properties of
the previous section. The proposition says that formula (4) for this `K₀`
and holomorphic families of inducing vectors gives formula (4) for every
`K` and fixed inducing vectors. The module states it and does not prove it.
The following argument shows why it holds; it is not formalized.

1. **The compact subgroup `K₀`.** Apply `TruncationOrthogonalProjectionStatement`
   to `r.data.i` and `r.data.ν`; `r.isCompatible.maximalSplit` and
   `r.isCompatible.generic` supply its hypotheses. Reflection data exist by
   `GroupScheme.relativeRootReflectionExistence`, and `hρ₀` is
   `ArthurTruncation.bijective_restrictToTorus_minimal`. The parabolic `P`
   contains `P₀`, so `P(𝔸)K₀ = G(𝔸)`. The parabolic `P'` contains the minimal
   parabolic of `r'`, which is `γP₀γ⁻¹` for a rational point `γ`
   (`GroupScheme.minimalParabolicConjugacy`). Iwasawa coverage passes to
   conjugates (`AdelicGroupPoints.IsIwasawaCompact.of_conjugate_map`) and to
   larger subgroups, so `P'(𝔸)K₀ = G(𝔸)`.
2. **The archimedean part.** Maximal compact subgroups of `G(F_∞)` are
   conjugate
   (`InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy`). Choose
   `t ∈ G(F_∞)` such that `K₁ = t⁻¹Kt` has the archimedean part of `K₀`; its
   finite part is that of `K`. Write `R(s)f(g) = f(gs)`, replace each inducing
   vector `v` by `v₁ = R(t⁻¹)v`, that is `v₁(x) = v(xt⁻¹)`, and let
   `a_P(λ) = exp⟨λ, H_P^{K₁}(t)⟩` be the height power of `K₁` along `P` at `t`
   (`heightPower`), an entire nowhere vanishing function of `λ`; likewise
   `a_{P'}` along `P'`. By `eisensteinConjugateCompactTransport`,
   `E_{P,K₁}(v₁, λ)(gt) = a_P(λ) E_{P,K}(v, λ)(g)`, and the normalized
   intertwining operators satisfy the same identity with the scalar
   `a_P(λ) / a_{P'}(wλ)`. Put `E₁,j(λ)(g) = a_P(λ) E_j(λ)(gt⁻¹)` and
   `c₁,j(x) = c_j(x) / a_P(i e(x))`, multiply the expansion coefficients by
   `a_P(λ) / a_{P'}(wλ)` and replace the vectors `ψ` by `R(t⁻¹)ψ`, and do the
   same for `P'`. These are data for `K₁`. Their packet satisfies
   `Θ₁(gt) = Θ(g)`, that is `Θ₁ = R(t⁻¹)Θ`, and likewise `Θ'₁ = R(t⁻¹)Θ'`.
   Right translation preserves the quotient Haar measure (compare
   `AdelicGroupPoints.rationalQuotientL2RightAction`), so square integrability
   and the inner product do not change. On the right side of (4) the scalars
   combine to `1 / |a_{P'}(wλ)|²`, which is `1` for imaginary `λ`.
3. **The finite part.** `K₁` and `K₀` have the same archimedean projection.
   By `eisensteinFiniteCompactChange`, the twist `φ_λ` for `K₁` of an
   automorphic inducing function is a finite sum
   `∑_u e^{⟨λ, u⟩} (cut_u φ)_λ` of twists for `K₀` of fixed automorphic
   functions. Hence `E_{P,K₁}(φ, λ) = ∑_u e^{⟨λ, u⟩} E_{P,K₀}(cut_u φ, λ)` on
   the regular region: one fixed vector for `K₁` becomes a holomorphic family
   for `K₀` with exponential coefficients.
4. **Why families are needed.** The continuation of `E_{P,K₁}(φ, ·)` given
   with the data supplies the regularity near the support of the transported
   combination `∑_u e^{⟨λ, u⟩} E_{P,K₀}(cut_u φ, ·)`. It says nothing about the
   separate series `E_{P,K₀}(cut_u φ, ·)`: their continuation and holomorphy
   near the support would require another argument. For the intertwining
   operators, Lapid's Working hypothesis gives holomorphy on `i𝔞_P^*` (§2,
   p.312). For the Eisenstein series of individual vectors of `A^2_P`,
   holomorphy on `i𝔞_P^*` is Lapid's Proposition 6 (p.329), which he deduces
   from Proposition 2, so it is not available in a proof of Proposition 2. The
   family statement asks only for the regularity of the combinations, which
   the transported data have; the fixed-vector statement
   `LocalWavePacketInnerProductTruncationCompactStatement` asks for the
   regularity of each piece.
5. **The remaining data.** The pieces `cut_u φ` lie in `A^2_P` for `K₀`:
   they are automorphic for the common archimedean compact by
   `eisensteinFiniteCompactChange`, equivariant under `A_M`, and square
   integrable. The expansions of `M(w, λ)` transform the same way. The
   heights along `P'` for `K₁` and `K₀` differ by a function with finitely
   many values, so the coefficients are multiplied by exponentials of `wλ` and
   the vectors `ψ` are cut along the level sets. A Haar measure on `M'(𝔸)`
   compatible with `K₀` exists (`iwasawaCompatibleMeasureExistence`). The inner
   product `(·,·)_{P'}` on `A^2_{P'}` is that of
   `L²(A_{M'} U'(𝔸) M'(F) \ G(𝔸))` and does not depend on the compact
   subgroup used to compute it. Pieces cut along different level sets are
   orthogonal, and for imaginary `λ` the exponential factors have absolute
   value `1`. So the right side of (4) for the `K₀` data is the right side for
   the original data.

## Scope

The module contains the two statements, the proved implication between them,
and the proposition `LocalWavePacketCompactChangeStatement`. It does not prove
Lapid's Proposition 2 in either form, the limit of truncated inner products,
or the change of compact subgroup.
