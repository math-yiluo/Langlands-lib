# The `(G, M)`-family of the main terms in Lapid's §8

Module `Langlands.Global.LocalWavePacketMainTermFamilyStatement` states
`Langlands.Global.WavePacketMainTermFamilyStatement`. The file states the proposition and does
not prove it.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page = printed page + 9), §8,
  p.328. Following Arthur, Lapid groups (18) into `(G, M)`-families indexed by `s ∈ Ω(P, P)`.
  The substitution printed below (18) is `sλ' − λ`. The parameter in (18), with `t' = t s`, is
  `tλ + t' conj(λ') = t(λ − sλ')` on the imaginary axis. Thus for
  `Λ = λ − sλ'` the kernel in Lemma 8 is `c_Q(T; Λ) / θ_Q(Λ)` and the coefficient is
  `d_Q(λ; Λ) = (φ(λ + μ), M_{Q|P}(λ)⁻¹ M_{Q|P}(s, s⁻¹(λ − Λ)) φ'(s⁻¹(λ − Λ) + μ))_P`.
  Reflecting the variable leaves the wall condition and the value at `Λ = 0` unchanged.
  That value is `(φ(λ + μ), M(s, s⁻¹λ) φ'(s⁻¹λ + μ))_P` and gives the summand in (4) by
  adjointness.
- J. Arthur, *On a family of distributions obtained from Eisenstein series II: Explicit
  formulas*, Amer. J. Math. 104 (1982), registered as `arthur-1982-eisenstein-distributions-II`
  (PDF page = printed page − 1288): §1, pp.1292–1295, the operators `M_{P₁|P}(s, λ)`, the
  functional equations (1.1)–(1.2), the rank-one formula (1.3) (for `r` in `W^L(𝔞_M, 𝔞_{M₁})`,
  the elements fixing `𝔞_L` pointwise, the operator depends only on the projection of `λ` onto
  `(𝔞_M^L)^*`), and the rewriting of the main term with `Q = t⁻¹P₁`; §2, pp.1296–1299, the
  definition of `d_Q` and the proof that `{d_Q}` is a `(G, M)`-family by (1.3).

## The data

The setting is that of `WavePacketMainTermLimitStatement`
(`Langlands/Global/LocalWavePacketMainTermLimitStatement.lean`), without the coordinates, the
cutoffs and the wave-packet coefficients, which do not enter. For standard parabolic subgroups
`P = P_J`, `P' = P_{J'}`:

- `φ_j(λ) = ∑_l b_{j,l}(λ) v_{j,l}` and `φ'_{j'}(λ') = ∑_{l'} b'_{j',l'}(λ') v'_{j',l'}`, with
  `v_{j,l} ∈ A^2_P`, `v'_{j',l'} ∈ A^2_{P'}` and entire coefficients;
- representatives `(w t, cw t)` of elements of `Ω(P, P')` and expansions
  `M(w t, λ) φ_j(λ) = ∑_a coeff_{t,j,a}(λ) ψ_{t,j,a}` in `A^2_{P'}`;
- for every standard `S`, representatives `(wS S t, cwS S t)` of elements of `Ω(P, S)` and
  `(wS' S t', cwS' S t')` of elements of `Ω(P', S)`, and expansions
  `M(t, λ)φ_j(λ) = ∑_a coeffS_{S,t,j,a}(λ) ψS_{S,t,j,a}`,
  `M(t', λ')φ'_{j'}(λ') = ∑_{a'} coeffS'_{S,t',j',a'}(λ') ψS'_{S,t',j',a'}` in `A^2_S`.

All expansions hold for `Re λ` sufficiently regular (`IsStandardRegularParameter`), and the
coefficients are meromorphic in linear coordinates with domains `DM`, `DMS`, `DMS'`; by the
definition of `IsMeromorphicInCoordinatesOn` these domains are open and the coefficients are
holomorphic on them. The representatives need not be distinct or exhaust the Weyl sets.

For coordinates `e : ℝⁿ ≃ 𝔞_S^*` and a weight `β`, the Lean `let` `innerS S t t' j j' n e β λ λ'`
is

`F^{e,β}_{S,t,t'}(λ, λ') = ∑_{a, a'} coeffS_{S,t,j,a}(λ) · conj(coeffS'_{S,t',j',a'}(λ')) ·
(ψS_{S,t,j,a}, ψS'_{S,t',j',a'})_S`,

the inner product being `inducedInnerProduct K _ _ _ (μM S) e β` (Lapid's `(·,·)_S` for the
measure on `𝔞_S` given by the coordinates dual to `e`, when `∫ β = 1`). For imaginary `λ ∈ DMS`,
`λ' ∈ DMS'` it is `(M(t, λ)φ_j(λ), M(t', λ')φ'_{j'}(λ'))_S`, the inner product in the main term
of Lapid's formula (2).

## The statement

Both clauses concern imaginary parameters `λ = i x`, `λ' = i x'` (`imaginaryParameter`).

1. **`(G, M)`-family property.** Let `(ws, cs)` be a Weyl conjugation from `P_S` to `P_{S₂}`
   whose real parameter map `s = realWeylParameter _ cs (π S₂)` fixes the hyperplane
   `⟨μ, α^∨⟩ = 0` of `𝔞_S^*` pointwise, as a subspace of `𝔞_0^*` (after `restrictToTorus`),
   for a simple root `α ∉ S`. Let `t₂ ∈ ΩS S₂`, `t₂' ∈ ΩS' S₂` with
   `weylParameter (cwS S₂ t₂) = s ∘ weylParameter (cwS S t)` and likewise for `t₂'`, `t'`. If
   `λ ∈ DMS`, `λ' ∈ DMS'` and `⟨tλ + t' λ̄', α^∨⟩ = 0`, then
   `F^{e,β}_{S,t,t'}(λ, λ') = F^{e₂,β}_{S₂,t₂,t₂'}(λ, λ')` for all coordinates `e` of `𝔞_S^*`,
   the transported coordinates `e₂ = s ∘ e` of `𝔞_{S₂}^*` and every continuous compactly
   supported `β` with `∫ β = 1`.

   In Arthur's terms: the element `s` is the elementary symmetry of `W^L(𝔞_S, 𝔞_{S₂})`, `L` the
   Levi subgroup with `Δ_0^L = S ∪ {α}`, or the identity. With `ν = tλ` and `ν' = t'λ'` the
   functional equation gives `M(t₂, λ) = M(s, ν) M(t, λ)` and `M(t₂', λ') = M(s, ν') M(t', λ')`;
   the condition says that `ν` and `ν'` have the same projection to `(𝔞_S^L)^*` (on the imaginary
   axis `λ̄' = −λ'`), so `M(s, ν) = M(s, ν')` by (1.3), and this operator is unitary on the
   imaginary axis for the measures that correspond under `s`. This is the compatibility of
   `d_Q` and `d_{Q'}` on the common wall of adjacent chambers in Arthur 1982, pp.1298–1299.
2. **Value at the origin.** Let `t₀ ∈ ΩS J` represent the identity of `Ω(P, P)`, `w = w tw`
   represent an element of `Ω(P, P')` and `t' ∈ ΩS' J` its inverse
   (`weylParameter (cwS' J t') ∘ weylParameter (cw tw) = id`). If `λ ∈ DM ∩ DMS` and
   `wλ ∈ DMS'`, then

   `F^{e,β}_{P,t₀,t'}(λ, wλ) = ∑_a ∑_{l'} coeff_{tw,j,a}(λ) · conj(b'_{j',l'}(wλ)) ·
   (ψ_{tw,j,a}, v'_{j',l'})_{P'}`,

   the inner product on the right being `inducedInnerProduct` for `μM'`, the transported
   coordinates `e₂ = w ∘ e` of `𝔞_{P'}^*` and `β`. The left side is
   `(φ_j(λ), M(t', wλ) φ'_{j'}(wλ))_P`, the right side `(M(w, λ)φ_j(λ), φ'_{j'}(wλ))_{P'}`: this
   is the adjointness `M(t', wλ)^* = M(w, λ)` on the imaginary axis. With `s = t'` it is the
   value `d_P(λ; 0)` of Lapid's family and the summand of the right side of (4).

## Use

`Langlands.Global.WavePacketMainTermLimitReductionStatement` (module
`Langlands.Global.LocalWavePacketMainTermLimitReduction`) takes this proposition, with
`StandardChamberParametrizationStatement`, as a premise of Lapid's §8 limit.
