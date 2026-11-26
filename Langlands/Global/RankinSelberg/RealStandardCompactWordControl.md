# Compact-direction control of word derivatives in the compact Banach real standard module

Module `Langlands.Global.RankinSelberg.RealStandardCompactWordControl`, namespace
`Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach`.

The module states `RealStandardCompactWordControlStatement`: in the compact Banach
realization of a real standard module of `GL_{r+1}(ℝ)`, the Banach norm of any word
derivative of a smooth vector is bounded by a constant times a finite sum of Banach norms of
word derivatives along skew-symmetric matrices, that is, along the Lie algebra of the
orthogonal group. The module states this assertion and does not prove it. It contains no
other declaration.

## Conventions

* `n = r + 1`, `G = GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, and `K = O(n)` is
  `Matrix.unitaryGroup (Fin n) ℝ`. Real `n × n` matrices are the tangent directions of the
  matrix model `matrixModel ℝ n` of `G`.
* `ds : List RealBlock` is a list of real blocks: a real character has rank one, a real
  induction of a complex character has rank two, and `realRank ds` is the sum of the block
  ranks. The hypothesis `realRank ds = r + 1` says that the blocks fill the `r + 1` diagonal
  positions.
* `realStandardModule n ds` is the real standard module: the smooth functions `f` on `G` with
  `f(diag(a) u g) = χ(a) f(g)` for `u` upper unipotent, where `χ` is the character
  `principalSeriesCharacter ℝ n (realPositionCharacter ds)` of the diagonal torus, and whose
  Fourier coefficients of weight `|k| < |m|` along the rotations in the coordinates of every
  induction block of weight `m` vanish.
* `Carrier n ds`, `embed ds` and `representation ds` are those of the module
  `RealStandardCompactBanachAction`. `Carrier n ds` is the closure, in the sup norm on the
  continuous functions `C(O(n), ℂ)`, of the restrictions to `O(n)` of the functions of
  `realStandardModule n ds`, with that sup norm. `representation ds` is the jointly continuous
  action of `G` on it which acts on the restriction of a smooth standard function by right
  translation.
* `smoothVectors (matrixModel ℝ n) (representation ds)` is the space of genuine smooth vectors:
  the vectors `v` whose orbit map `g ↦ π(g) v` is real smooth. For a word
  `Xs = [X₁, …, Xₖ]` of real matrices, `iteratedLieDerivative (matrixModel ℝ n) π Xs v` is the
  genuine iterated derivative `dπ(X₁) ⋯ dπ(Xₖ) v` of the orbit map, and the empty word gives
  `v`. Its norm `‖dπ(Xs) v‖` is the norm of `Carrier n ds`, and it equals the genuine word
  seminorm `wordSeminorm (matrixModel ℝ n) π Xs v` of the module `SmoothDerivative`
  (`wordSeminorm_apply`).
* A real matrix `Y` is skew-symmetric when `Yᵀ = -Y`; these matrices form the Lie algebra
  `𝔬(n)` of `O(n)`.

## The statement

`RealStandardCompactWordControlStatement` is the proposition: for every `r : ℕ`, every
`ds : List RealBlock` with `realRank ds = r + 1` and every word `Xs` of real
`(r + 1) × (r + 1)` matrices, there exist a finite set `T` of words of real
`(r + 1) × (r + 1)` matrices and a real number `C` such that

1. `0 ≤ C`;
2. every letter `Y` of every word `w ∈ T` satisfies `Yᵀ = -Y`;
3. for every smooth vector `v` of `representation (n := r + 1) ds`, writing `π` for this
   representation,

   `‖dπ(Xs) v‖ ≤ C ∑_{w ∈ T} ‖dπ(w) v‖`.

The set `T` and the constant `C` depend on `r`, `ds` and `Xs`, not on `v`. The set `T` may
contain the empty word, whose term is the Banach norm `‖v‖`.

## Derivation

The assertion is an internal consequence of the compact Iwasawa differential formula; it is
not transcribed from a statement of the literature. The following argument explains why it
holds.

1. **Reduction to standard functions.** By `realStandardCompactSmoothVectors`, every smooth
   vector of `representation ds` is `embed ds f` for a unique `f` in
   `realStandardModule n ds`, and the genuine Banach derivative along `X` corresponds to the
   scalar right derivative `R_X f(g) = d/dt f(g exp(tX))` at `t = 0`, which preserves
   `realStandardModule n ds`. The Banach norm of `embed ds f` is `sup_{k ∈ O(n)} |f(k)|`. It
   therefore suffices to bound `sup_K |R_{X₁} ⋯ R_{Xₖ} f|` by a constant times a finite sum of
   `sup_K |R_w f|` over words `w` in `𝔬(n)`.
2. **The splitting.** Every real matrix `A` is uniquely `A = B + Z` with `B` upper triangular
   and `Z` skew-symmetric: if `L` is the strictly lower triangular part of `A`, then
   `Z = L - Lᵀ` and `B = A - Z`. Both parts depend linearly on `A`.
3. **The first-order formula on `K`.** Let `h` be in the principal series and `k ∈ O(n)`.
   Since `k exp(tX) = exp(t kXk⁻¹) k`, split `kXk⁻¹ = B(k) + Z(k)`. The derivative at `t = 0`
   of `h(exp(tA) k)` is linear in `A`. Along the upper triangular part, `exp(tB)` is the
   product of the diagonal matrix with entries `exp(t Bᵢᵢ)` and an upper unipotent matrix, so
   the left covariance gives the term `dχ(B(k)) h(k)`, with `dχ` the derivative of the torus
   character, a linear form in the diagonal entries. Along the skew part,
   `exp(t Z) k = k exp(t k⁻¹Z k)` and `Y(k) = k⁻¹ Z(k) k` is skew-symmetric because `k` is
   orthogonal. Hence

   `R_X h(k) = c_X(k) h(k) + R_{Y(k)} h(k)`, with `c_X(k) = dχ(B(k))`.

   Writing `Y(k) = ∑ⱼ a_{X,j}(k) Eⱼ` in a basis `(Eⱼ)` of `𝔬(n)`, the functions `c_X` and
   `a_{X,j}` are polynomial in the entries of `k`.
4. **Words.** On `K`, the right derivative along `Eⱼ` is the derivative of the restriction
   `h|_K` along the left-invariant vector field `Eⱼ` of `O(n)`. So restriction to `K`
   intertwines `R_X` with the first-order operator `D_X = c_X + ∑ⱼ a_{X,j} Eⱼ`, whose
   coefficients are smooth on `K`. Since each `R_X` preserves the standard module,
   `(R_{X₁} ⋯ R_{Xₖ} f)|_K = D_{X₁} ⋯ D_{Xₖ} (f|_K)`. The Leibniz rule expands
   `D_{X₁} ⋯ D_{Xₖ}` as a sum, over the words `w` of length at most `k` in the basis `(Eⱼ)`,
   of smooth coefficients `b_w` on `K` times the derivative along `w`. The restriction of
   `R_w f` to `K` is that derivative of `f|_K`.
5. **Bound.** The coefficients `b_w` are continuous on the compact group `K`, hence bounded.
   With `T` the set of these basis words (it contains the empty word) and `C` the largest
   bound of the coefficients, step 1 gives the inequality. The words produced have length at
   most that of `Xs`; the statement does not record this bound.

The calculation uses only the left covariance under the upper triangular Borel subgroup. The
vanishing Fourier coefficients attached to the rank-two induction blocks define a subspace of
the principal series that every `R_X` preserves, so the same calculation applies to the
standard modules of lists containing induction blocks. The argument does not use the
hypothesis `realRank ds = r + 1`; the statement is restricted to these lists, whose standard
modules are the standard modules of `GL_{r+1}(ℝ)`.

## Use

The bound compares the topology of all genuine word seminorms with the seminorms along
compact directions alone. Let `V` be a space with linear operators `dσ(Y)` for `Y ∈ 𝔬(n)`,
written `dσ(w)` for their compositions along words `w`, and let `S` be a linear map from `V`
into the smooth vectors of `representation ds` with `S dσ(Y) u = dπ(Y) S u` for `Y ∈ 𝔬(n)` and
`‖S u‖ ≤ q(u)` for a seminorm `q` on `V`. For every word `Xs`, the statement gives

`‖dπ(Xs) S u‖ ≤ C ∑_{w ∈ T} ‖dπ(w) S u‖ = C ∑_{w ∈ T} ‖S dσ(w) u‖ ≤ C ∑_{w ∈ T} q(dσ(w) u)`.

If `q` and every `dσ(Y)` with `Y ∈ 𝔬(n)` are continuous on `V`, for instance when `V` is a
space of smooth vectors with its word-derivative topology, `dσ` its derivatives and `q` one
of its word seminorms, then each `q ∘ dσ(w)` is a continuous seminorm, and `S` is continuous
for the word-derivative topology of its target although it need not commute with the
noncompact derivatives.
