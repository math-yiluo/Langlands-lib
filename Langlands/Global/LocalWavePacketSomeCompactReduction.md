# Lapid's Proposition 2 for holomorphic families and one compact subgroup

Module `Langlands.Global.LocalWavePacketSomeCompactReduction` states three
propositions and proves one implication:

- `Langlands.Global.LocalWavePacketSectionSomeCompactStatement`: for the
  parabolic data of `LocalWavePacketInnerProductStatement` there is a maximal
  compact `K` with `P(𝔸)K = P'(𝔸)K = G(𝔸)` for which Lapid's formula (4) holds
  for all wave packets whose inducing vectors are holomorphic families
  `λ ↦ ∑_i b_i(λ) v_i` with entire coefficients `b_i`;
- `Langlands.Global.TruncatedWavePacketSectionSomeCompactLimitStatement`: there
  is such a `K`, with in addition `P_0(𝔸)K = G(𝔸)` for the minimal parabolic
  `P_0` of `r` and the projection property of the full-quotient truncation,
  for which the sufficient condition with which Lapid begins the proof of
  Proposition 2 (§8) holds for the same data;
- `Langlands.Global.localWavePacketSectionSomeCompact_of_limit` (theorem): the
  second statement implies the first;
- `Langlands.Global.LocalWavePacketSomeCompactChangeStatement`: the implication
  `LocalWavePacketSectionSomeCompactStatement →
  LocalWavePacketInnerProductStatement`.

The module proves neither of the first two statements and does not prove
`LocalWavePacketSomeCompactChangeStatement`; it is a proposition whose truth is
explained below.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9).
  - §2, p.311: one maximal compact `K` "in good position with respect to
    `M_0`", fixed throughout, `A^2_P`, `φ_λ(g) = φ(g) e^{⟨λ, H_P(g)⟩}`, the
    Eisenstein series; p.312: the intertwining operators, the Working
    hypothesis and its consequence that `M(w, λ)` is unitary, hence
    holomorphic, for `λ ∈ i𝔞_P^*`, and the truncation operator `Λ^T`.
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
  suitable maximal compact `K` with `G(𝔸) = P_0(𝔸)K`; §13, Proposition 13.1
  and the paragraph after its proof, pp. 68–69: `Λ^T` extends to an orthogonal
  projection on `L²`.
- J. Arthur, *The trace formula in invariant form*, Ann. of Math. 114 (1981),
  registered as `arthur-1981-trace-formula-invariant-form`: §1, p.9, maximal
  compact subgroups admissible relative to `M_0`, cited by Arthur 2005, p.24,
  for the choice of `K`.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §2.2: the twist
  `φ_λ` defined with the Iwasawa height of the chosen compact subgroup.
- A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965),
  registered as `borel-tits-1965-groupes-reductifs`, Théorème 4.13: minimal
  parabolic subgroups over `F` are conjugate by a rational point (in the
  Library, `GroupScheme.minimalParabolicConjugacy`).

## Holomorphic families of inducing vectors

The data of `LocalWavePacketSectionSomeCompactStatement` after the choice of
`K` are those of `LocalWavePacketInnerProductStatement` (module
`Langlands.Global.AdelicLocalWavePacketStatement`) with respect to `K`, with
the fixed inducing vectors replaced by families:

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
not the series `E_{P,K}(v j i, ·)`. Two differences remain. The coefficients
`b j i` are entire functions of `λ`, not smooth functions on `i𝔞_P^*`, because
`E j` is tied to the convergent series on the regular region; the smooth
dependence on `x` is carried by `c j`. And, as in
`LocalWavePacketInnerProductStatement`, only a neighbourhood of the support is
required to lie in the domain of holomorphy (local regularity), not all of
`i𝔞_P^*`.

## The compact subgroup

Lapid fixes one maximal compact `K` in good position with respect to `M_0`
(p.311) and proves Proposition 2 for it. The two statements of this module
assert, for every choice of the parabolic data `F`, `G`, `P`, `r`, `P'`, `r'`,
`π'` and the hypotheses `hG`, `hU`, `hU'`, `hlπ'`, that some compact subgroup
works:

- `LocalWavePacketSectionSomeCompactStatement`: some
  `K : Subgroup (AdelicGroupPoints F G)` with `hK : IsIwasawaCompact p K`,
  `hK' : IsIwasawaCompact p' K` and `IsMaximalCompactSubgroup F G K`, such that
  the conclusion above holds for all data with respect to `K` (all `rho`,
  `hsmooth`, `hcalc`, measures, families and expansions).
- `TruncatedWavePacketSectionSomeCompactLimitStatement`: some such `K` with
  also `hK₀ : IsIwasawaCompact (Standard.parabolicHom r.data.i r.data.ν ∅) K`
  and, for all reflection data `D₀` and comparisons `hρ₀`, some `C` such that
  `truncation hG r.isCompatible.maximalSplit D₀ hK₀ hρ₀ T` satisfies
  `IsOrthogonalL2Extension` for `rationalQuotientHaarMeasure F G` whenever every
  simple root of `(r.data.i, r.data.ν)` exceeds `C` at `T`; and the limit
  described in the next section holds for all data with respect to `K`.

The source-backed witness is a compact subgroup admissible relative to the
minimal Levi subgroup of `r.data.i` in the sense of Arthur 1981, §1, p.9. It is
the suitable `K` of Arthur 2005, p.24, for which Proposition 13.1 and the
projection property hold; we read Lapid's good position as this
admissibility, so Lapid's Proposition 2, and the limit with which §8 proves
it, hold for it. `P` contains `P_0`, so `P(𝔸)K = G(𝔸)`; `P'` contains the
minimal parabolic of `r'`, which is `γP_0γ⁻¹` for a rational point `γ`
(Borel–Tits, `GroupScheme.minimalParabolicConjugacy`), and Iwasawa coverage
passes to conjugates (`AdelicGroupPoints.IsIwasawaCompact.of_conjugate_map`)
and to larger subgroups. The statements assert nothing for other compact
subgroups.

## `TruncatedWavePacketSectionSomeCompactLimitStatement`

For the compact subgroup `K` it provides, the data of
`LocalWavePacketSectionSomeCompactStatement` with respect to `K`, any
reflection data `D₀` and comparison `hρ₀`, and any direction `v₀` on which every
simple root of `(r.data.i, r.data.ν)` is positive; the statement quantifies
over all of them. With `f(y) = Θ(y.out)`, `f'(y) = Θ'(y.out)` on
`G(F) \ G(𝔸)` and `trunc j` the full-quotient truncation with respect to `K`
at the parameter `j • v₀`, the conclusion is:

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
`LocalWavePacketTruncationReduction`. Lapid's §8 derives the limit from
Proposition 1 for the same compact subgroup, which is why the projection
property and the limit are asserted for one `K`.

## The theorem `localWavePacketSectionSomeCompact_of_limit`

Fix the parabolic data. `TruncatedWavePacketSectionSomeCompactLimitStatement`
gives `K` with `hK`, `hK'`, `hK₀`, maximality, the projection property and the
limit; the proof offers `K`, `hK`, `hK'` and maximality for
`LocalWavePacketSectionSomeCompactStatement`. For the remaining data it takes
reflection data `D₀` from `GroupScheme.relativeRootReflectionExistence` and
the comparison `hρ₀` from `ArthurTruncation.bijective_restrictToTorus_minimal`,
with `r.isCompatible.maximalSplit` and `r.isCompatible.generic`. It applies the
limit with the direction `v₀ = 1 ⊗ r.data.ν`, on which every simple root is
positive (`cocharacter_simple_pos`), and obtains items 1–4. Then
`ArthurTruncation.fullQuotientTruncationPairing`, with
`ArthurTruncation.truncationFiniteness` and the projection property for `D₀`,
`hρ₀`, turns items 1–4 into `MemLp f 2 μG`, `MemLp f' 2 μG` and
`∫ f · conj f' dμG = ` the right side of (4). The measure `μG` of the
conclusion is `rationalQuotientHaarMeasure F G` by definition.

## `LocalWavePacketSomeCompactChangeStatement`

`LocalWavePacketInnerProductStatement` is stated for every maximal compact `K`
with `P(𝔸)K = P'(𝔸)K = G(𝔸)` and fixed inducing vectors. The proposition says
that formula (4) for one such compact subgroup `K₁` and holomorphic families of
inducing vectors, for every choice of the parabolic data, gives this. The
module states it and does not prove it. The following argument shows why it
holds; it is not formalized.

1. **The compact subgroup `K₁`.** Given the data of
   `LocalWavePacketInnerProductStatement` with a compact subgroup `K`, apply
   `LocalWavePacketSectionSomeCompactStatement` to the same parabolic data. It
   gives `K₁`, maximal, with `P(𝔸)K₁ = P'(𝔸)K₁ = G(𝔸)`.
2. **The archimedean part.** Maximal compact subgroups of `G(F_∞)` are
   conjugate
   (`InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy`). Choose
   `t ∈ G(F_∞)` such that `K₂ = t⁻¹Kt` has the archimedean part of `K₁`; its
   finite part is that of `K`, and `P(𝔸)K₂ = P'(𝔸)K₂ = G(𝔸)` (write
   `t⁻¹ = pk` with `p ∈ P(𝔸)`, `k ∈ K`). Write `R(s)f(g) = f(gs)`, replace each
   inducing vector `v` by `v₂ = R(t⁻¹)v`, that is `v₂(x) = v(xt⁻¹)`, and let
   `a_P(λ) = exp⟨λ, H_P^{K₂}(t)⟩` be the height power of `K₂` along `P` at `t`
   (`heightPower`), an entire nowhere vanishing function of `λ`; likewise
   `a_{P'}` along `P'`. By `eisensteinConjugateCompactTransport`,
   `E_{P,K₂}(v₂, λ)(gt) = a_P(λ) E_{P,K}(v, λ)(g)`, and the normalized
   intertwining operators satisfy the same identity with the scalar
   `a_P(λ) / a_{P'}(wλ)`. Put `E₂,j(λ)(g) = a_P(λ) E_j(λ)(gt⁻¹)` and
   `c₂,j(x) = c_j(x) / a_P(i e(x))`, multiply the expansion coefficients by
   `a_P(λ) / a_{P'}(wλ)` and replace the vectors `ψ` by `R(t⁻¹)ψ`, and do the
   same for `P'`. These are data for `K₂`. Their packet satisfies
   `Θ₂(gt) = Θ(g)`, that is `Θ₂ = R(t⁻¹)Θ`, and likewise `Θ'₂ = R(t⁻¹)Θ'`.
   Right translation preserves the quotient Haar measure (compare
   `AdelicGroupPoints.rationalQuotientL2RightAction`), so square integrability
   and the inner product do not change. On the right side of (4) the scalars
   combine to `1 / |a_{P'}(wλ)|²`, which is `1` for imaginary `λ`.
3. **The finite part.** `K₂` and `K₁` have the same archimedean projection.
   By `eisensteinFiniteCompactChange`, the twist `φ_λ` for `K₂` of an
   automorphic inducing function is a finite sum
   `∑_u e^{⟨λ, u⟩} (cut_u φ)_λ` of twists for `K₁` of fixed automorphic
   functions. Hence `E_{P,K₂}(φ, λ) = ∑_u e^{⟨λ, u⟩} E_{P,K₁}(cut_u φ, λ)` on
   the regular region: one fixed vector for `K₂` becomes a holomorphic family
   for `K₁` with exponential coefficients.
4. **Why families are needed.** The continuation of `E_{P,K₂}(φ, ·)` given
   with the data supplies the regularity near the support of the transported
   combination `∑_u e^{⟨λ, u⟩} E_{P,K₁}(cut_u φ, ·)`. It says nothing about the
   separate series `E_{P,K₁}(cut_u φ, ·)`: their continuation and holomorphy
   near the support would require another argument. For the intertwining
   operators, Lapid's Working hypothesis gives holomorphy on `i𝔞_P^*` (§2,
   p.312). For the Eisenstein series of individual vectors of `A^2_P`,
   holomorphy on `i𝔞_P^*` is Lapid's Proposition 6 (p.329), which he deduces
   from Proposition 2, so it is not available in a proof of Proposition 2. The
   family statement asks only for the regularity of the combinations, which
   the transported data have.
5. **The remaining data.** The pieces `cut_u φ` lie in `A^2_P` for `K₁`:
   they are automorphic for the common archimedean compact by
   `eisensteinFiniteCompactChange`, equivariant under `A_M`, and square
   integrable. The expansions of `M(w, λ)` transform the same way. The
   heights along `P'` for `K₂` and `K₁` differ by a function with finitely
   many values, so the coefficients are multiplied by exponentials of `wλ` and
   the vectors `ψ` are cut along the level sets. A Haar measure on `M'(𝔸)`
   compatible with `K₁` exists (`iwasawaCompatibleMeasureExistence`). The inner
   product `(·,·)_{P'}` on `A^2_{P'}` is that of
   `L²(A_{M'} U'(𝔸) M'(F) \ G(𝔸))` and does not depend on the compact
   subgroup used to compute it. Pieces cut along different level sets are
   orthogonal, and for imaginary `λ` the exponential factors have absolute
   value `1`. So the right side of (4) for the `K₁` data is the right side for
   the original data.

## Scope

The module contains the two statements, the proved implication between them,
and the proposition `LocalWavePacketSomeCompactChangeStatement`. It does not
prove Lapid's Proposition 2 in either form, the limit of truncated inner
products, or the change of compact subgroup.
