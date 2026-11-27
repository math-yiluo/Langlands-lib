# Continuity of the open-cell integrand

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellContinuity`, namespace
`Langlands.Global.CuspidalPairEisenstein.OpenCellContinuity`.

The module proves that for a standard additive character `ψ`, a section `φ` with
`IsSection T T' φ` and every `s ∈ ℂ`, the open-cell integrand
`Y ↦ W_M(φ_s)(w u'(Y)) · conj(ψ_N(u'(Y)))` of
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md) is
continuous on `M_((t+1)×(r+1))(𝔸)`; in particular it is almost everywhere strongly measurable for
every Borel measure. Here `φ_s = Oneplace.twisted φ s = φ · H^s` and `W_M` is
`CuspidalPairEisenstein.leviWhittaker`. The results about sections `φ` assume, as the statement
does, that the adele quotient is compact (`[CompactSpace (AdeleQuotient F)]`).

## Content

- **`continuous_whittaker_param`**: let `ψ` be a standard additive character, `P` a topological
  space and
  `h : P → GL_(n+1)(𝔸) → ℂ` (on the points of the group scheme `GL_(n+1)`) be jointly continuous,
  with each `h p` left invariant under the rational points. Then
  `p ↦ generalLinearWhittakerFunction F n ψ 1 (h p) 1` is continuous.
- `continuous_heightPower` from `CuspidalPairEisensteinUnfoldingSeries`: Shahidi's power `H(g)^s` (`heightPower F r t s`) is continuous.
- `leviEmbedding_rationalLevi`: the block-diagonal embedding commutes with the rational points.
- `Unfolding.leviPair_mul`, `Unfolding.continuous_leviPair`, `continuous_leviPair'`: `diag(x, y)` is multiplicative
  and continuous in `(x, y)`.
- `exists_rational_of_mem`: a rational point of the group scheme `GL_n` is, as an adelic matrix,
  the image of a rational matrix.
- `continuous_of_isSection` from `CuspidalPairEisensteinUnfoldingSeries` and `OpenCellContinuity.continuous_twisted`: `φ` and `φ_s` are continuous.
- `twisted_leviPair_rational_mul`, `twisted_leviPair_left`, `twisted_leviPair_right`: `φ_s` is
  left invariant under `diag(γ₁, γ₂)` for rational `γ₁ ∈ GL_(r+1)(F)`, `γ₂ ∈ GL_(t+1)(F)`.
- `innerWhittaker ψ φ s G x`: the inner Whittaker coefficient
  `W_(t+1)(y ↦ φ_s(diag(x, y) G))(1)`; `continuous_innerWhittaker` (jointly continuous in
  `(G, x)`) and `innerWhittaker_rational_mul` (left invariant in `x` under rational points).
- **`continuous_leviWhittaker`**: for a standard `ψ` and `IsSection T T' φ`,
  `G ↦ W_M(φ_s)(G)` is continuous on `GL_N(𝔸)`.
- `Unfolding.openCellUnipotent_zero`, `continuous_openCellUnipotent`.
- **`continuous_openCellIntegrand`**: for a standard `ψ` and `IsSection T T' φ`, the open-cell
  integrand is continuous.

## Proofs

- `continuous_whittaker_param` follows the proof of
  `RankinSelbergGlobal.Unfolding.continuous_cuspWhittaker'` (module
  `Langlands.Global.RankinSelberg.DualExpansionFinal`). The Whittaker coefficient is the integral
  over the compact quotient `N_(n+1)(F) \ N_(n+1)(𝔸)` (probability measure) of
  `h p (u) · conj(χ(u))` at the representative `u`; by the invariance of `h p` and of the
  generic character under rational unipotent points, this integrand is the lift of a function on
  `P × N(F) \ N(𝔸)` that is continuous because `id × (quotient map)` is a quotient map.
  `CuspidalWhittaker.continuous_integral_of_continuous_uncurry` gives continuity of the
  integral in `p`.
- `continuous_heightPower`: `heightPower_eq_schemeHeightPower` identifies `H^s` with the
  group-scheme height power of the standard maximal compact subgroup, which is continuous
  (`IsIwasawaCompact.continuous_heightPower`).
- `continuous_of_isSection`: `φ` is the underlying function of the smooth compact-finite block
  section `smoothSection hφ` (module `Langlands.Global.Factors.CuspidalPairSchemeAutomorphy`),
  continuous by `continuous_smoothBlockSection`.
- `twisted_leviPair_rational_mul`: `diag(γ₁, γ₂)` is the rational point of the parabolic given by
  the Levi element `(γ₁, γ₂)`, and `φ` and `H^s` are left invariant under the rational points of
  the parabolic (`isSection_rational_mul`, `heightPower_rational_mul`).
- `continuous_leviWhittaker`: `continuous_whittaker_param` applied first to the inner
  coefficient with parameter `(G, x)` (invariance by `twisted_leviPair_right`), then to the outer
  coefficient with parameter `G` (invariance by `innerWhittaker_rational_mul`, which uses
  `twisted_leviPair_left`).
- `continuous_openCellUnipotent`: the matrix of `u'(Y)` is a reindexed block matrix
  `[[I, Y], [0, I]]`, continuous in `Y`, and `u'(Y)⁻¹ = u'(-Y)`
  (`Oneplace.openCellUnipotent_add`).
- `continuous_openCellIntegrand`: `continuous_leviWhittaker` composed with
  `Y ↦ w u'(Y)`, times `conj(ψ(Y_(t,0)))` (`openCellUnipotent_superdiagonal_sum`), with `ψ`
  continuous.

## Provenance

The integral whose integrand is shown to be continuous here is the two-block `GL` open-cell
integral of [CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md):
an integral over the adelic `(t+1) × (r+1)` matrices `Y`, whose matrices `u'(Y)` form the
unipotent radical `U'` of the upper parabolic subgroup of `GL_(r+t+2)` with the two blocks
exchanged, of the Levi Whittaker coefficient `W_M` at `w u'(Y)`. The coefficient `W_M` is itself
given by two Whittaker integrations over the left quotients `N_(r+1)(F) \ N_(r+1)(𝔸)` and
`N_(t+1)(F) \ N_(t+1)(𝔸)` for the two diagonal blocks. It is analogous to the open-cell
expression for split `G₂` in Shahidi, *Functional equation satisfied by certain L-functions*,
Compositio Math. 37 (1978) (`shahidi-1978-functional-equation`), Lemma 2.1, formula (2.10),
p. 181, and the surviving Bruhat-cell integral in its proof, p. 182 (PDF pages 12–13). The
ambient group and parabolic are fixed in §§1–2: `G` is a simple group of type `G₂` split over
`ℚ` (§1, p. 173, PDF page 4), and `P = MN` is a maximal parabolic subgroup whose unipotent radical
`N` is generated by the five root spaces of `α, α + β, 2α + β, 3α + β, 3α + 2β`, while `°U` is
the unipotent radical of a Borel subgroup of `°G ≅ PSL₂` (§2, p. 176, PDF page 7). In Shahidi's
conventions (right `G_F`-invariant functions, Iwasawa decomposition `g = k m n`) and for
`Re(s) < -1/2`, the lemma writes the Fourier coefficient of the Eisenstein series as
`∫_(u ∈ °U_𝔸/°U_F) ∫_(u' ∈ N_𝔸) Φ_s(g u' w₀ u) conj(χ(u u')) du' du`. Shahidi remarks (p. 173)
that these computations can be done for an arbitrary Chevalley group and that `G₂` was chosen
for simplicity. Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981)
(`shahidi-1981-certain-l`), whose §§4–5 work with a reductive group split over `ℚ` (§1.2, p. 300,
PDF page 5), invokes "Lemma 2.1 and computations in Section 4 of [23]" in the proof of
Theorem 5.1, p. 351 (PDF page 56). In the `GL` integral the radical integral over `N_𝔸`
corresponds to the integral over `Y`, and the quotient integral over `°U_𝔸/°U_F` to the two
Whittaker integrations along the blocks of the Levi subgroup `GL_(r+1) × GL_(t+1)`; the `GL`
integral is not a specialization of Shahidi's `G₂` formula.

Neither source discusses the measurability of the integrand. The continuity proved here is the
Library's argument furnishing the almost-everywhere strong measurability of the `GL` open-cell
integrand needed for its integrability, and it is carried out directly for the `GL` integral:
`φ_s` is continuous and left invariant under the rational points of the two-block Levi subgroup,
each of the two Whittaker integrations over a compact quotient `N(F) \ N(𝔸)` preserves
continuity in the remaining variables (`continuous_whittaker_param`), and the integrand is
`W_M(φ_s)` composed with the continuous map `Y ↦ w u'(Y)`, times the continuous character factor
`conj(ψ(Y_(t,0)))`. The descent of the integrands to the compact quotients and the
parameter-dependent integration follow the Library's proof of
`RankinSelbergGlobal.Unfolding.continuous_cuspWhittaker'`.
