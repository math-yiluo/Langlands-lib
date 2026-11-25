# The difference operator of Bernstein–Lapid §8.5

Module `Langlands.Global.AdelicIntertwiningDifferenceStatement` serves
`Langlands.Global.IntertwiningWeakMeromorphicContinuationStatement` (module
`Langlands.Global.AdelicIntertwiningContinuationReduction`; its reduction is in
`Langlands.Global.AdelicIntertwiningWeakContinuationReduction`). It states
`Langlands.Global.IntertwiningConstantTermDifferenceStatement` as a proposition definition. It
supplies no proof.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. Journal pages are those of the PDF
in that folder, with PDF page = journal page − 186; TeX line numbers refer to `1911.02342.tex`.

- §8.5, *Meromorphic continuation of intertwining operators*, pp. 224–225 (TeX lines
  3417–3486). This covers:
  - the Lemma on regular `a ∈ A_Q`;
  - the statement `E^Q(M(w', λ)(C_{P,P_{w'}}φ), w'λ) ∈ 𝒜_Q(w'(μ_{P_{w'}} + λ))`;
  - the difference operator `D(λ) = ∏_{w' ∈ _QW_P \ {w}} D_a^{Q, w'(μ_{P_{w'}} + λ) − wλ}`;
  - the identity `D(λ)((C_{G,Q} E(φ, λ))_{−wλ}) = D(λ)(M(w, λ)φ)`;
  - the polynomials `f(x) = ∏_i (x − a^{w((μ_P)_i)})` and
    `g(λ, x) = ∏_{w' ≠ w} ∏_i (x − a^{w'((μ_{P_{w'}})_i + λ) − wλ})`;
  - the sentence "The polynomials `f` and `g(λ, ·)` are coprime for generic `λ`";
  - "`f(T_a) = 0` and the restriction `D̃(λ)` of `D(λ)` to `𝒜_Q(wμ_P)` is `g(λ, T_a)`".
- §6.6, *Polynomial exponential functions*, pp. 205–206 (TeX lines 1540–1623): the spaces
  `PE_V(μ)` and the difference operators `D_v^λ`, (6.13), the spaces `𝒜_P(μ)` (6.14), and
  (6.15) `M(w, λ)φ ∈ 𝒜_Q(wμ)`.
- §6.2, *Cuspidal exponents*, p. 201 (TeX lines 1222–1257): the twisted action (6.2)
  `a · φ(g) = δ_P(a)^{−1/2} φ(ag)` and (6.4) `M(w, λ)φ ∈ 𝒜_{Q, wμ}`.
- Lemma 6.10, the constant term formula (6.17)
  `C_{G,Q} E(φ, λ) = ∑_{w ∈ _QW_P} E^Q(M(w, λ)(C_{P,P_w}φ), wλ)`, p. 208 (TeX lines 1729–1760).

## Statement

The data and hypotheses are exactly those of
`Langlands.Global.IntertwiningMeromorphicContinuationStatement` and of
`Langlands.Global.IntertwiningWeakMeromorphicContinuationStatement`, in the same order and at
the same universe:

- a number field `F` and a connected reductive `G`;
- a parabolic `p : P → G` with geometric unipotent radical `iU`, rational Levi `l : M → P`
  and presentation `r`;
- a parabolic `q : Q → G` with unipotent radical `iV : V → Q`, rational Levi `l' : M' → Q`
  with `Q = M' ⋉ V`, and a retraction `π'` with `l' ≫ π' = 𝟙 M'`;
- `(w, c)` with `IsWeylConjugation p l q l' w c`;
- `K` maximal compact with `hK : IsIwasawaCompact p K` and `hK' : IsIwasawaCompact q K`;
- a closed `rho`, the data `hsmooth`, `hcalc`, and `φ ∈ 𝒜_P`, i.e. `IsAutomorphicFunctionOn`
  for `parabolicQuotientSubgroup F p iU l`.

The conclusion asserts the existence of the following:

- a point `t : AdelicGroupPoints F G`;
- a polynomial `f : ℂ[X]`;
- a number `k` and functions `root : Fin k → ComplexCharacterParameter F P → ℂ`.

They satisfy three conditions.

1. Every `root j` is entire in linear coordinates: `root j ∘ e` is complex differentiable on
   `ℂⁿ` for every complex linear isomorphism `e : ℂⁿ ≃ X^*(P) ⊗ ℂ`.
2. There is `λ₀` with `f.eval (root j λ₀) ≠ 0` for every `j`. Equivalently, `f` and
   `∏ j (X − root j λ₀)` have no common root, so they are coprime.
3. There is `R₀` such that for every `λ` with `r.IsRegularParameter hA hT R₀ λ`:
   - `IsTranslationPolynomialSolution t f (M(w, λ)φ)`;
   - `IsTranslationPolynomialSolution t (∏ j (X − C (root j λ))) Δ_λ`, where
     `Δ_λ(x) = m_Q(x)^{−wλ} · C_Q E(φ, λ)(x) − M(w, λ)φ(x)`.

Here `IsTranslationPolynomialSolution t D ψ` (module `AdelicLocalFinitenessStatement`) means
`∑_k D_k ψ(t^k x) = 0` for every `x ∈ G(𝔸)`, i.e. `D(T_t)ψ = 0` for the plain left
translation `T_t ψ(x) = ψ(tx)`. The Library terms are:

- `M(w, λ)φ` is `hK.intertwiningOperator hK' iU l iV c π' w φ λ`;
- `m_Q(x)^{−wλ}` is `hK'.heightPower (-weylParameter l c π' λ) x`;
- `C_Q E(φ, λ)(x)` is `subgroupConstantTerm F (iV ≫ q) (hK.eisensteinSeries φ λ) x`, the
  constant term along `V` of the Eisenstein series, with `vol(V(F) \ V(𝔸)) = 1`.

## Correspondence with the source

Provenance: derived. BL do not state this assertion separately. It collects the facts that
§8.5 uses before the resultant is formed. The Library objects correspond to BL's as follows:

- `t` is BL's regular element `a ∈ A_Q`, embedded in `G(𝔸)` through `q` and `l'`.
- `f` is BL's `f`, up to normalization. BL's `T_a` is the twisted action
  `a · φ = δ_Q(a)^{−1/2} φ(a ·)` of (6.2). Plain left translation is `δ_Q(a)^{1/2}` times it,
  so the roots of `f` are `δ_Q(a)^{1/2} a^{w((μ_P)_i)}`. The first identity of condition 3 is
  `M(w, λ)φ ∈ 𝒜_Q(wμ_P)` ((6.15)) together with the description of `𝒜_Q(μ)` by difference
  operators in §6.6. It holds with the same `f` for all `λ` at which the intertwining integral
  converges.
- `∏ j (X − root j λ)` is BL's `g(λ, ·)`, normalized for plain translation and the twist. For
  `x ∈ G(𝔸)` and `t ∈ Q(𝔸)`, `m_Q(tx)^{−wλ} = m_Q(t)^{−wλ} m_Q(x)^{−wλ}`
  (`IsIwasawaCompact.height_map_mul`). Hence `T_t(ψ_{−wλ}) = c(λ) (T^{tw}_t ψ)_{−wλ}` with
  `c(λ) = δ_Q(t)^{1/2} m_Q(t)^{−wλ}`, where `T^{tw}_t` is the twisted action of (6.2).
  The roots are therefore
  `root_{w',i}(λ) = δ_Q(t)^{1/2} · t^{w'((μ_{P_{w'}})_i + λ)} · m_Q(t)^{−wλ}`, an exponential of
  an affine function of `λ`, which is entire in linear coordinates (condition 1). The second
  identity of condition 3 is BL's `D(λ)((C_{G,Q}E(φ, λ))_{−wλ}) = D(λ)(M(w, λ)φ)`. It follows
  from (6.17) by separating the term of the double coset of `w`. For `w ∈ W(P, Q)` one has
  `Q_w = Q`, so that term is `[M(w, λ)φ]_{wλ}`. Every other term lies in
  `𝒜_Q(w'(μ_{P_{w'}} + λ))` and is killed by `D(λ)` after the twist.
- Condition 2 is BL's sentence "`f` and `g(λ, ·)` are coprime for generic `λ`", evaluated at
  one point. By the Lemma of §8.5, for `w' ≠ w` the vector `w'^{−1}H_Q(a) − w^{−1}H_Q(a)` does
  not lie in `𝔞_0^P`. So each `root_{w',i}` is the exponential of a nonconstant affine
  function of `λ ∈ 𝔞_{P,ℂ}^*`. It equals a root of `f` only on a proper analytic subset, and a
  point `λ₀` outside the finite union of these subsets exists. If `_QW_P = {w}`, then `k = 0`
  and condition 2 holds trivially.
- The regular region `r.IsRegularParameter hA hT R₀` is that of the Library's convergence
  statements. For large `R₀` the Eisenstein series converges absolutely
  (`Langlands.Global.eisensteinAbsoluteConvergence`), and so does the intertwining integral
  (`Langlands.Global.intertwiningAbsoluteConvergence`). So both sides are BL's convergent
  expressions there. The Markdown of `IntertwiningMeromorphicContinuationStatement` explains
  why `Q` need not be standard and `K` need not be in good position. Those reductions apply
  unchanged.

## Use

`Langlands.Global.intertwiningWeakMeromorphicContinuation_of_difference` (module
`AdelicIntertwiningWeakContinuationReduction`) proves
`IntertwiningWeakMeromorphicContinuationStatement` from this statement and
`EisensteinMeromorphicContinuationStatement`. That proof forms BL's recovery formula with
`∏ j (f(root j λ) − f)` in place of `v(λ, ·) g(λ, ·)` and `∏ j f(root j λ)` in place of the
resultant `R(λ)`.

## Scope

The statement is not proved here. A proof needs:

- the constant-term formula (6.17) (`Langlands.Global.EisensteinConstantTermStatement`,
  unproved in the Library);
- the exponent theory `𝒜_Q(μ)` with (6.15);
- the regular element `a ∈ A_Q`;
- the Lemma of §8.5.

The statement asserts nothing about the uniqueness or minimality of `f` and of the roots, about
`t` beyond the displayed identities, or about parameters outside the regular region.
