# The equal-rank Whittaker integrand on one Iwasawa cell

Module `Langlands.Global.RankinSelberg.EqualEulerPointwise`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualEulerPointwise`.

## Content

Notation. `n = r + 1`. `F` is a number field, `ψ` a unitary character of `𝔸` trivial on
`F`, `T`, `T'` actual cuspidal realizations of `GL_n` with spectral presentations `P`,
`P'`, and `S` a finite set of finite places containing `P.exceptional` and
`P'.exceptional` such that every finite component of `ψ` outside `S` has conductor `𝒪_v`
(`FiniteAdditiveSupport ψ S`). `x`, `x'` are vectors fixed by `GL_n(𝒪_w)` at every finite
`w ∉ S` (`IsSphericalOutside`), `W = cuspWhittaker F T ψ x` is the `ψ`-Whittaker function of
`x` and `W' = cuspWhittaker F T' ψ⁻¹ x'` the `ψ⁻¹`-Whittaker function of `x'`. `Φ` is a
function on adelic row vectors that is standard outside `S` (`IsStandardOutside`: it
vanishes off `𝒪_w^n` at every finite `w ∉ S` and there depends only on the coordinates at
`S` and the archimedean places). `e_n g = lastRow F r g` is the last row of `g` and
`detPower F n g s = |det g|_𝔸 ^ s`.

For a finite place `v ∉ S`, `N(v) = Ideal.absNorm v.asIdeal` is its absolute norm,
`ϖ_v = placeUniformizer v` the uniformizer of `F_v` from module
`LocalPointFactorization`, `ϖ_v ^ λ = torus ϖ_v λ` for `λ ∈ ℤ^n`, and `ι_v(h)` the adelic
point with component `h` at `v` and `1` elsewhere (`localPoint`). `a`, `b` are tuples
enumerating the Satake parameters of `P` and `P'` at `v`
(`Eigenvalues.ofTuple a = P.spectralSystem.eigenvalues v _`, and likewise for `b`).
`halfModulus q λ = δ_B^(1/2)(ϖ ^ λ) = q ^ (-(∑_i (n - 1 - 2i) λ_i)/2)` (indices
`i = 0, …, n - 1`) and `satakeSchur a λ = s_λ(a)` are the Library's normalizations in
Shintani's formula, and `spectralPoint q s = q ^ (-s)`.

### Definitions and local identities

- `cellMultiplier q a b s λ` is
  `(δ^(1/2) s_λ(a) if λ is antitone, else 0) · (δ^(1/2) s_λ(b) if λ is antitone, else 0) ·
  ((q ^ (-s)) ^ (λ_1 + ⋯ + λ_n) if λ_n ≥ 0, else 0)`, with `δ^(1/2) = halfModulus q λ`.
  Here `λ_1 + ⋯ + λ_n ≥ 0` whenever `λ` is antitone with `λ_n ≥ 0`; the exponent is taken
  through `Int.toNat`. This is `W°_a(ϖ ^ λ) W°_b(ϖ ^ λ) Φ°(e_n ϖ ^ λ) |det ϖ ^ λ|^s`.
- `modulusExponent_eq`: the exponent `modulusExponent λ = ∑_(i<j) (λ_i - λ_j)` of
  `WhittakerCellDecompositionStatement` equals `∑_i (n - 1 - 2i) λ_i`.
- `zpow_modulusExponent_mul_cellMultiplier`: for `q > 0`,
  `q ^ modulusExponent λ · cellMultiplier q a b s λ = equalRankLocalTerm a b (q ^ (-s)) λ`,
  the local term of module `EqualEulerLocalSum`. So the inverse modulus `δ_B⁻¹(ϖ ^ λ)`
  times the cell multiplier is the summand whose sum over `λ` is the pair Euler factor.
- `residueCardinality_canonical v`: the residue cardinality of the canonical realization of
  `padicField v` is `N(v)`. `absNorm_pos v`: `0 < N(v)`.

### The pointwise identity

Both theorems assume `UnramifiedWhittakerFactorizationStatement` (the one-place
factorization of spherical global Whittaker functions by Shintani's formula, Cogdell 2004
§2.2) as the hypothesis `hA`; they do not prove it. Let `v ∉ S` and let `g ∈ GL_n(𝔸)`
satisfy `g_v ∈ N_n(F_v) GL_n(𝒪_v)` (`IsUnipotentIntegral`).

- `whittaker_mul_localPoint_torus`:
  `W(ι_v(ϖ_v ^ λ) g) W'(ι_v(ϖ_v ^ λ) g) =
  (δ^(1/2) s_λ(a) if λ antitone, else 0) · (δ^(1/2) s_λ(b) if λ antitone, else 0) ·
  W(g) W'(g)` with `δ^(1/2) = halfModulus N(v) λ`.
- `integrand_localPoint_torus_mul` (the pointwise identity): with `h = ι_v(ϖ_v ^ λ) g`,
  `W(h) W'(h) Φ(e_n h) |det h|^s = cellMultiplier N(v) a b s λ · W(g) W'(g) Φ(e_n g) |det g|^s`.

## Provenance

Internal supporting results for the proof of `EqualEulerFactorizationStatement` (Cogdell
2004, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart: §2.3, printed p.210,
with Theorem 3.3, p.215). Cogdell computes the unramified local equal-rank integral on the
Iwasawa cells `N ϖ ^ λ K`: there the integrand is
`δ_B⁻¹(ϖ ^ λ) W°(ϖ ^ λ) W'°(ϖ ^ λ) Φ°(e_n ϖ ^ λ) |det ϖ ^ λ|^s`, and Shintani's formula
gives the values of `W°` (computation of Jacquet, Piatetski-Shapiro and Shalika, recalled
in Cogdell's Fields lectures, Lecture 7 §3, printed pp.57–58). The Library's one-place cell
decomposition `WhittakerCellDecompositionStatement` works with the global integrand on
classes with `g_v ∈ N GL(𝒪_v)` translated by `ι_v(ϖ_v ^ λ)`. This module supplies the
global pointwise form of the cell computation: the translated integrand is the original one
times the cell multiplier. The decomposition of the multiplier into its four factors is the
local computation above. The cancellation of the generic characters of `ψ_v` and `ψ_v⁻¹`
inside the cell functions (lemma `cellFunction_mul_cellFunction` of
`LocalPointFactorization`) replaces the usual evaluation at `g_v = ϖ ^ λ`.

## Proof

- **Local identities.** `modulusExponent_eq` is the identity `sum_sub_of_lt_eq` of
  `EqualEulerLocalSum` after writing the inner sum over `Finset.Ioi i` as a filtered sum. `zpow_modulusExponent_mul_cellMultiplier` is
  `torusTerm_eq_equalRankLocalTerm` of `EqualEulerLocalSum` after this rewriting.
  `residueCardinality_canonical` is `HeckeEulerProduct.residueCardinality_eq` transported
  along `topologicalData_eq_canonicalTopologicalData`; `absNorm_pos` follows from
  `one_lt_absNorm`.
- **Whittaker part.** Take the component `ψ_v` of `ψ` with conductor `𝒪_v` from
  `FiniteAdditiveSupport`, and let `θ`, `θ'` be the standard and inverse standard
  characters of `N_n(F_v)` it defines, so that `θ(u) θ'(u) = 1`. Write `g_v` for the
  component of `g` at `v`, `g' = g ι_v(g_v)⁻¹` (so `g'_v = 1`) and `t = ϖ_v ^ λ`. Then
  `g = g' ι_v(g_v)` and `ι_v(t) g = g' ι_v(t g_v)` (`localPoint_mul_eq`). The hypothesis
  `hA`, applied with the uniformizer `ϖ_v` (uniformizing for the canonical valuation by
  `isUniformizingElement_canonical`) at the points `t g_v` and `g_v`, gives
  `W(g' ι_v(h)) = W(g') W°_θ(h; a)` and `W'(g' ι_v(h)) = W'(g') W°_θ'(h; b)` for
  `h = t g_v` and `h = g_v`; the residue cardinality there is `N(v)` by
  `residueCardinality_canonical`. Writing `g_v = u k` with `u` unitriangular and `k`
  integral (`exists_eq_mul_of_isUnipotentIntegral`), the exponent of `t g_v` is `λ` and
  that of `g_v` is `0` (`exponent_torus_mul`, `exponent_unipotent_mul_integral`). Then
  `sphericalWhittaker_mul_sphericalWhittaker` evaluates
  `W°_θ(t g_v; a) W°_θ'(t g_v; b)` and its `_of_exponent_eq_zero` form gives
  `W°_θ(g_v; a) W°_θ'(g_v; b) = 1`. The identity follows by `linear_combination`.
- **Pointwise identity.** Rewrite the Whittaker part with `whittaker_mul_localPoint_torus`.
  The Schwartz part `Φ(e_n ι_v(ϖ_v ^ λ) g) = (Φ(e_n g) if λ_n ≥ 0, else 0)` is
  `EqualEulerSchwartz.apply_lastRow_localPoint_torus` (module `EqualEulerSchwartzPart`,
  with `ϖ_v` uniformizing for `Valued.v` by `isUniformizingElement_valued`). The
  determinant part is `detPower_localPoint_mul` with
  `log ‖det ϖ_v ^ λ‖ = -(∑ λ_i) log N(v)` (`log_norm_det_torus`). Then split cases. If
  `λ` is antitone and `λ_n ≥ 0`, then `∑ λ_i ≥ 0`, and
  `exp(s · log N(v) ^ (-∑ λ_i)) = (N(v) ^ (-s)) ^ (∑ λ_i)` by
  `exp_mul_log_zpow_eq_spectralPoint_pow` of `EqualEulerLocalSum`. Otherwise one of the
  factors is `0` on both sides. Each case closes by `ring`.
