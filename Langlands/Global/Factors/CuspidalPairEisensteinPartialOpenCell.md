# Partial open-cell integrals of a cuspidal-pair Eisenstein series

Module `Langlands.Global.Factors.CuspidalPairEisensteinPartialOpenCell`, namespace
`Langlands.Global.CuspidalPairEisenstein`. It imports
`Langlands.Global.Factors.CuspidalPairEisensteinOpenCell`, whose Markdown
[CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md) fixes the
notation: `N = r + t + 2`, the upper two-block parabolic `P = MU` with blocks of sizes
`r + 1` and `t + 1`, Shahidi's block Weyl representative `w = openCellWeyl F r t`, the
matrix `u'(Y) = openCellUnipotent F r t Y` of the exchanged radical `U'` for an adelic
`(t + 1) × (r + 1)` matrix `Y`, the Levi Whittaker coefficient `leviWhittaker`, the twist
`heightPower` and the Haar measure `openCellHaar` on `M_((t+1)×(r+1))(𝔸)` for its Borel
σ-algebra.

## Definitions

- `IsSphericalOutside F r t S φ`, for a finite set `S` of finite places and
  `φ : GL_N(𝔸) → ℂ`: for every finite place `v ∉ S`, every `k ∈ GL_N(𝒪_v)`
  (`FiniteAdelicGL.localIntegral F N v`) and every `g`,
  `φ(g · ι_v(k)) = φ(g)`, where `ι_v(k)` is the adelic point with component `k` at `v` and
  `1` at every other place (`AdelicGL.ofFinite` of `FiniteAdelicGL.localInclusion`).
- `IsSphericalSectionOutside T T' S φ` (for actual cuspidal realizations `T`, `T'` of
  `GL_(r+1)`, `GL_(t+1)`): `φ` is spherical outside `S` in the previous sense, and for every
  `k` in the standard maximal compact subgroup `standardCompact F (r+t+2)` the normalized
  Levi slice `m ↦ δ_P(m)^(−1/2) φ(m k)` on the adelic Levi `FullLevi F (blockShape r t)`
  lies in the complex span of the products `m ↦ x(m₁) y(m₂)`, where `x` runs over the
  vectors of `T` and `y` over the vectors of the contragredient realization
  `dualRealization T'` that are fixed by `GL(𝒪_v)` at every finite place `v ∉ S`
  (`RankinSelbergGlobal.IsSphericalOutside`). This is the slice condition of
  `CuspidalPairEisenstein.IsSection`, with the cusp forms restricted to those spherical
  outside `S`. A section induced from cusp forms that are spherical outside `S`, with a
  local section at each finite place outside `S` that is the normalized spherical vector,
  has this property.
- `integralOutside F r t S`: the set `U_S` of adelic matrices
  `Y ∈ M_((t+1)×(r+1))(𝔸)` such that every entry `Y_(ij)` has component in
  `𝒪_v = v.adicCompletionIntegers F` at every finite place `v ∉ S` (`finiteProjection`).
  There is no condition at the places of `S` or at the archimedean places.
- `openCellIntegrand ψ φ s Y`: the integrand
  `W_M(φ_s)(w u'(Y)) · conj(ψ_N(u'(Y)))` of `openCellIntegral`, with
  `φ_s = φ · heightPower F r t s` and `ψ_N(u) = ψ(∑_i u_(i,i+1))`. It is written exactly as in
  `openCellIntegral`, and `openCellIntegral_eq_integral` records (by `rfl`) that
  `openCellIntegral ψ φ s = ∫ openCellIntegrand ψ φ s d(openCellHaar F r t)`.
- `partialOpenCellIntegral ψ S φ s`: the partial open-cell integral
  `I_S(φ, s) = ∫_(U_S) openCellIntegrand ψ φ s d(openCellHaar F r t)`, a Bochner integral for
  the Borel σ-algebra used by `openCellHaar`. Its convergence is not asserted here.

## Mathematical meaning and provenance

The definitions are internal. They express the splitting of the open-cell integral used in
the proof of Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981), Theorem 5.1,
pp. 351–352 (registered as `shahidi-1981-certain-l`). For a factorizable section the
coefficient is the product over all places of the local Jacquet–Whittaker values `W_v(e_v)`,
and Shahidi writes it as `∏_(v ∈ S) W_v(e_v) · ∏_(v ∉ S) W_v(e_v)` (p. 352).

Let `φ = ⊗_v φ_v` be a factorizable section built from cusp forms spherical outside `S`
(in the sense of `IsSphericalSectionOutside`) and let every finite component of `ψ` outside
`S` have conductor `𝒪_v`. At a finite place `v ∉ S` and for
`Y_v ∈ M_((t+1)×(r+1))(𝒪_v)`, the local unipotent `u'(Y_v)` and `w` lie in `GL_N(𝒪_v)` and
`ψ_v` is trivial on `Y_v`, so the factor of the integrand at `v` is its value at the
identity, the value `⁰W_v(e_v)` at the identity of the Levi Whittaker function of the
spherical inducing data. Shahidi normalizes the spherical inducing vector `φ_v` so that
`⁰W_v(e_v) = 1` for all `v ∉ S` (p. 352); with
this normalization `I_S(φ, s)` is the integral over the places of `S` and the archimedean
places only, which is the adelic form of Shahidi's semilocal factor `∏_(v ∈ S) W_v(e_v)`,
up to the positive constant comparing `openCellHaar` with a product of local measures, and
the remaining places contribute `∏_(v ∉ S) W_v(e_v) = L^S(1 + s, π × π')⁻¹`. These two facts
are the content of the statements `CuspidalPairEisensteinUnramifiedFactorizationStatement`
and `CuspidalPairEisensteinSemilocalNumeratorStatement`; the definitions here assert
neither. For spherical data normalized otherwise the factor at `v ∉ S` on `M(𝒪_v)` is the
scalar `⁰W_v(e_v)`; these scalars can be absorbed into the local data at the other places.
The unramified factorization statement compares `I` and `I_S` of the same section and needs
no normalization.
