# The unramified value of the two-block open-cell sum

Module `Langlands.Representation.Shahidi.UnramifiedOpenCellSumStatement`, namespace
`Langlands.Shahidi`. The module states one proposition and two auxiliary definitions; it
proves nothing.

## Definitions

- `integralMatrices K a b`: the additive subgroup of `a × b` matrices over the `p`-adic field
  `K` whose entries lie in the ring of integers `𝒪 = K.canonicalTopologicalData.Integers`
  of the canonical valuation.
- `twoBlockModulus K m₁ m₂ = |det m₁|^n / |det m₂|^m` for `m₁ ∈ GL_m(K)`, `m₂ ∈ GL_n(K)`,
  with the residue-normalized absolute value
  (`K.canonicalTopologicalData.determinantNorm`). This is the modulus character `δ_P` of the
  upper two-block parabolic `P` of `GL_(m+n)(K)` on its Levi factor; compare
  `PadicField.TopologicalData.leviModulus_twoBlocks`.

## Statement

`UnramifiedOpenCellSumStatement.{u}`: for ranks `r`, `t` and real bounds `A`, `B` there is a
real `σ` such that the following holds for every prime `p`, every `p`-adic field
`K : PadicField.{u} p` (with its canonical local-field structure, residue cardinality `q`),
every unitary additive character `ψ` of `K` with additive conductor `0` (trivial on `𝒪`,
nontrivial on `ϖ⁻¹𝒪`), every uniformizer `ϖ` of the canonical valuation, and all tuples
`a : Fin (r + 1) → ℂˣ`, `c : Fin (t + 1) → ℂˣ` with `‖a_i‖ ≤ q^A` and `‖c_j⁻¹‖ ≤ q^B`.

Let `N = r + t + 2`, `σ < Re s`, and let `f : GL_((r+1)+(t+1))(K) → ℂ` satisfy

`f(u(X) · diag(m₁, m₂) · k) = δ_P(m₁, m₂)^(1/2 + s/N) · W°(m₁; a) · W°(m₂; c)`

for every `X ∈ M_((r+1)×(t+1))(K)`, `m₁ ∈ GL_(r+1)(K)`, `m₂ ∈ GL_(t+1)(K)` and
`k ∈ GL_((r+1)+(t+1))(𝒪)`. Here `u(X) = [[I, X], [0, I]]` is `Shahidi.upper`,
`diag(m₁, m₂)` is `GeneralLinear.blockSum`, `δ_P(m₁, m₂) = twoBlockModulus K m₁ m₂`, and
`W°(·; a) = GeneralLinear.Spherical.sphericalWhittaker hϖ θ q a` is the Library's explicit
spherical Whittaker function of `GL_(r+1)(K)` for the standard character `θ` of `ψ`
(Shintani's formula: its value at `u ϖ^λ k` is `θ(u) δ_B^(1/2)(ϖ^λ) s_λ(a)` for dominant `λ`
and `0` otherwise), and likewise `W°(·; c)` on `GL_(t+1)(K)`. Then

`∑_(Y ∈ M_((t+1)×(r+1))(K) / M_((t+1)×(r+1))(𝒪)) f(w u'(Y)) · conj(ψ(Y_(t,0)))
  = ∏_(i,j) (1 − a_i c_j⁻¹ q^(−(1+s)))`

as an unconditionally convergent sum (`HasSum`), where `w = Shahidi.blockWeyl (r+1) (t+1)`
is the block Weyl element `[[0, I_(r+1)], [I_(t+1), 0]]`, `u'(Y) =
Shahidi.intertwiningUnipotent (r+1) (t+1) Y = [[I_(t+1), Y], [0, I_(r+1)]]`, and the summand
is evaluated at the chosen representative `Quotient.out Y` of each class.

The summand does not depend on the representative: for `Z` integral, `u'(Y + Z) = u'(Y) u'(Z)`
with `u'(Z) ∈ GL(𝒪)`, and `ψ` is trivial on `𝒪`. The function `f` is determined by the
transformation law, since every element of `GL_((r+1)+(t+1))(K)` has the form
`u(X) diag(m₁, m₂) k`.

The functions `W°(·; a)` and `W°(·; c)` are defined by Shintani's formula for every tuple of
units. When `a` and `c` are the Satake parameters of irreducible generic unramified
representations `π₁` of `GL_(r+1)(K)` and `π₂` of `GL_(t+1)(K)` (this holds on a dense open
set of parameters, for instance when no two entries of `a`, nor of `c`, have ratio `q^(±1)`),
`W°(·; a)` and `W°(·; c)` are their normalized spherical Whittaker functions, and the law is
the one of the normalized spherical section `f°_s` of `Ind_P^G(π₁ ⊗ π₂ ⊗ δ_P^(s/N))`
composed with the Whittaker functional of the Levi that takes the value `1` on the spherical
vector. For arbitrary tuples the statement makes no representation-theoretic claim: the
law is an explicit condition on `f`. The source identity, proved by Casselman–Shalika for
unramified principal series, then passes to all tuples in the region of absolute
convergence, because for fixed `Y` and `s` the summand and the product are polynomial
functions of the entries of `a` and `c⁻¹` (by the signs of the Iwasawa weights on the open
cell, explained in the last section), and the absolutely convergent sum is locally uniform
in the parameters.

## Source

W. Casselman and J. Shalika, *The unramified principal series of p-adic groups II. The
Whittaker function*, Compositio Math. 41 (1980) (`casselman-shalika-1980-whittaker`),
Theorem 5.4, p. 227 (PDF page 22): the Whittaker function of the normalized spherical
vector of an unramified principal series, given by the Jacquet integral, takes at the
identity the value `∏_(α > 0) (1 − q^(−1) χ(a_α))`.

F. Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`),
proof of Theorem 5.1, p. 352 (PDF page 57): for `v ∉ S`, `W_v(e_v) = ∏_j L(1 + a_j s, π_v,
r_j)⁻¹`, by Casselman–Shalika, for the Whittaker functional of the induced representation
normalized so that the spherical value of the inducing data is `1`. For the upper two-block
parabolic of `GL_(r+t+2)`, `r_1 = Std ⊗ Std^∨` and `a_1 = r + t + 2` (§2.3, pp. 324–325).

F. Shahidi, *Fourier transforms of intertwining operators and Plancherel measures for
GL(n)*, Amer. J. Math. 106 (1984) (`shahidi-1984-fourier`), printed page 72, (0.2): the
local Jacquet integral `∫_(U') λ(f(w u')) conj(ψ(u')) du'` in the coordinates `w`, `U'` used
here.

## Comparison with the source

- The sum over `M(K)/M(𝒪)` is the Jacquet integral `∫_(U'(K)) … du'` for the Haar measure
  with `vol(M_((t+1)×(r+1))(𝒪)) = 1`, written as a sum because the integrand is invariant
  under `M(𝒪)`.
- In the inducing character `χ = (a q^(−s(t+1)/N), c q^(s(r+1)/N))` (that is, `π₁ ⊗
  |det|^(s(t+1)/N)` and `π₂ ⊗ |det|^(−s(r+1)/N)`, so that `δ_P^(s/N)` is the twist), the
  positive roots of the Levi cancel against the normalization of the Levi Whittaker
  functional, and each root `e_i − e_j` with `i` in the first block and `j` in the second
  contributes `1 − q^(−1) χ_i(ϖ)/χ_j(ϖ) = 1 − a_i c_j⁻¹ q^(−1−s)`.
- For `r = t = 0` the statement can be checked by hand: `w u'(y) = [[0, 1], [1, y]]`, and for
  `|y| = q^k > 1` its Levi part is `diag(y⁻¹, y)` up to units, so the summand is
  `(a c⁻¹ q^(−1−s))^k conj(ψ(y))`; the character sums over the shells `|y| = q^k` are `−1`
  for `k = 1` and `0` for `k ≥ 2`.
- The half-plane is uniform in `K`, `ψ`, `ϖ` and the parameters under the stated bounds,
  which bound `a` and `c⁻¹` from one side only. This uniformity is needed for the Euler
  product over all finite places of a number field. It comes from the shape of the open
  cell. With `m = r + 1` and `n = t + 1`, the matrix `w u'(Y)` has row blocks `[0, I_m]` and
  `[I_n, Y]`. In a factorization `w u'(Y) = u(X) diag(m₁, m₂) k`, right multiplication by
  `k⁻¹ ∈ GL(𝒪)` keeps the first row block integral, so `m₁` is integral and its Iwasawa
  weight `λ` is componentwise nonnegative (the bottom `j + 1` rows of an integral matrix
  have minors of valuation at least those of its bottom `j` rows). The second row block
  generates the lattice `𝒪^n + Y 𝒪^m`, which contains `𝒪^n`, so `m₂⁻¹` is integral and the
  Iwasawa weight `μ` of `m₂` is componentwise nonpositive. On these weights Shintani's
  formula and the bounds give `|s_λ(a)| ≤ C(λ) q^(A ∑_i λ_i)` and, using
  `s_μ(c) = s_(−w₀ μ)(c⁻¹)` (the Library theorem `Conductor.satakeSchur_inv`),
  `|s_μ(c)| ≤ C'(μ) q^(B ∑_j |μ_j|)`, where `C(λ)` and `C'(μ)` are numbers of semistandard
  tableaux, polynomial in the weights. Both `∑_i λ_i` and `∑_j |μ_j|` equal
  `D = ord(det m₁) = −ord(det m₂) ≥ 0`, the half-moduli `δ_B^(1/2)` are bounded by
  `q^(c D)` for a constant `c` depending on `r` and `t`, and `δ_P(m₁, m₂) = q^(−(m+n) D)`.
  The classes `Y` of depth `D` lie in `ϖ^(−D) M_(n×m)(𝒪) / M_(n×m)(𝒪)`, because
  `(𝒪^n + Y 𝒪^m)/𝒪^n` has length `D`, so there are at most `q^(m n D)` of them. Hence the
  sum of absolute values is at most `∑_(D ≥ 0) P(D) q^(−((m+n)(1/2 + Re s/N) − A − B − c − m n) D)`
  with `P` a polynomial depending only on `r` and `t` (here `A, B ≥ 0`, which may be
  assumed after enlarging the bounds), which converges uniformly for `Re s` beyond a bound
  depending only on `r`, `t`, `A`, `B`, since `q ≥ 2`.
- With `c` the Satake parameters of `(π'_v)^∨`, that is `c_j = b_j⁻¹` for the parameters `b`
  of `π'_v`, the value is `L(1 + s, π_v × π'_v)⁻¹ = ∏_(i,j) (1 − a_i b_j q^(−1−s))`.
