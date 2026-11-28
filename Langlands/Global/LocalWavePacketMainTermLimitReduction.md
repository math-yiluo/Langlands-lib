# Reduction of the limit of the integrated main terms in Lapid's §8

Module `Langlands.Global.LocalWavePacketMainTermLimitReduction` states
`Langlands.Global.WavePacketMainTermLimitReductionStatement`, the implication

`StandardChamberParametrizationStatement → WavePacketMainTermFamilyStatement →
WavePacketMainTermLimitStatement`.

The file states the implication and does not prove it.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*, Clay
Math. Proc. 13 (2011), registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`,
§8, p.328 (PDF page 337), after J. Arthur, Amer. J. Math. 104 (1982), §§1–2
(`arthur-1982-eisenstein-distributions-II`). The argument for the limit of (18) has four steps.

1. If `P` and `P'` are not associate, both sides vanish.
2. For associate parabolics, Lapid first reduces to `P' = P`. With `t' = t s`, the parameter in
   (18) on the imaginary axis is `tλ + t' conj(λ') = t(λ − sλ')`. Set `Λ = λ − sλ'` and evaluate
   the second vector at `λ' = s⁻¹(λ − Λ)`. The transported exponential and denominator then use
   the kernel `c_Q(T; Λ) / θ_Q(Λ)`, where `c_Q(T; Λ) = e^{Λ(Y_Q(T))}`. The sum is over
   `s ∈ Ω(P, P)` and `Q ∈ 𝓟(M)` with coefficients `d_Q(λ; Λ)` forming a `(G, M)`-family for
   each `s`. In the variable `L = sλ' − λ` printed below (18), the same kernel is
   `c_Q(T; −L) / θ_Q(−L)`.
3. Lemma 8 (`Langlands.GMFamily.OrthogonalSetLimitStatement`, proved as
   `Langlands.GMFamily.orthogonalSetLimit`) gives the limit of the inner integral, uniformly in
   `λ` and `μ`, as `∑_s d_P(λ; 0)`.
4. Adjointness and a change of variable give the right side of (4).

## The premises

- `StandardChamberParametrizationStatement` (module
  `Langlands.Global.LocalWavePacketMainTermChamberStatement`) supplies step 2 on the side of the
  Weyl sets: the sum over standard `S` and `t ∈ Ω(P, S)` is a sum over the chambers `Q ∈ 𝓟(M)`,
  with the simple roots, the wall relations and the orthogonal set `Y_Q(T)` needed for Lemma 8.
- `WavePacketMainTermFamilyStatement` (module
  `Langlands.Global.LocalWavePacketMainTermFamilyStatement`) supplies the `(G, M)`-family
  property of the inner products `(M(t, λ)φ(λ), M(t', λ')φ'(λ'))_S` in the main term and their
  value `(M(w, λ)φ(λ), φ'(wλ))_{P'}` at the origin, which is the adjointness of step 4.

The remaining steps of the implication are the change of variables and measure comparison,
the application of Lemma 8 with uniform bounds, and passage to the limit under the integral.
