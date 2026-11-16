# Basic properties of Whittaker functions of left invariant functions

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerBasic`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. Helper lemmas about the Whittaker function
`W_f = whittaker F r ψ f` (module `Interface`). Here
`W_f(g) = ∫_{N(F)\N(𝔸)} f(n g) ψ⁻¹(n_{12} + ⋯ + n_{r,r+1}) dn`, with `N` the upper unipotent
subgroup of `GL_{r+1}` and the normalized quotient measure. These facts are standard (Cogdell
2004, *Analytic theory of L-functions for GL_n*, §1). The proofs below are formal consequences of
the Library's `subgroupCharacterCoefficient` API.

## Section `Equivariance`

The hypotheses are a standard additive character `ψ` (`IsStandardAdditiveCharacter`) and a
function `f` on `GL_{r+1}(𝔸)` that is left invariant under `GL_{r+1}(F)`.

* `whittaker_mul_left`: `W_f(u g) = θ(u) W_f(g)` for `u ∈ N(𝔸)`, where `θ` is the Library's
  `genericCharacter F r ψ (fun _ => 1)`. Proof: the Library's
  `subgroupCharacterCoefficient_mul_left`, using that `θ` is a continuous unitary character trivial on
  `N(F)` and that `N(F)\N(𝔸)` is compact (`compactSpace_unipotentRationalQuotient`).
* `whittaker_colPoint_mul`: for `j < r` and a column `c ∈ 𝔸^{r+1}`, the column point
  `colPoint c = 1 + colMatrix_j(c)` (entries `c_a` at `(a, j+1)` for `a ≤ j`) acts by
  `W_f(colPoint(c) g) = ψ(c_j) W_f(g)`. Proof: by `whittaker_mul_left`. The superdiagonal sum of
  `1 + colMatrix_j(c)` is `c_j` (the Library's `sum_superdiag_one_add_colMatrix`).
* `whittaker_padRational_unipotent_mul`: `W_f(diag(n, I) z) = W_f(z)` for `n` in the rational upper
  unipotent subgroup of `GL_k(F)`, `k ≤ r + 1`. Proof: `diag(n, I)` lies in `N(𝔸)`. Its
  superdiagonal sum is the image of a rational number, on which `ψ` is trivial.
* `whittaker_padRational_of_rightRel`: `W_f(diag(γ, I) z)` depends only on the coset `N_k(F) γ`.
  Proof: write `b = (b a⁻¹) a` and apply the previous lemma.
* `whittaker_padRational_colPoint`: for `j < r`, `γ ∈ GL_{j+1}(F)` and a column `c` supported in
  the first `j + 1` coordinates (`IsColSupported`),
  `W_f(diag(γ, I) colPoint(c) y) = ψ(Σ_{a ≤ j} γ_{j,a} c_a) W_f(diag(γ, I) y)`. Proof: the
  Library's `padRational_mul_column` moves `diag(γ, I)` past the column point, which turns `c`
  into `γ c` (`colVec_eq_of_pointMatrix_eq`). Then `whittaker_colPoint_mul` applies, and
  `mulVec_padRational_row` identifies the `j`-th entry of `γ c`.

## Section `Integral`

* `norm_whittaker_le`: if `‖f(u g)‖ ≤ B` for all `u ∈ N(𝔸)`, then `‖W_f(g)‖ ≤ B`. Proof: the
  integrand has norm at most `B`, and the normalized quotient measure is a probability measure.
* `norm_whittaker_le_of_band`: a bound `B` for `f` on a band `lo ≤ |det x|_𝔸 ≤ hi` bounds `W_f`
  on the same band, since `|det(u g)|_𝔸 = |det g|_𝔸` for unipotent `u` (`detNorm_unipotent`).
* `whittaker_mul_right`: `W_f(g h) = W_{f(· h)}(g)`, by unfolding.
* `whittaker_mul_right_of_invariant`: if `f(x h) = f(x)` for all `x`, then `W_f(g h) = W_f(g)`.
* `whittaker_eq_setIntegral`: for continuous left invariant `f`, `W_f(g)` is a fixed constant times
  the Haar set integral of `f(n g) θ(n)⁻¹` over the Library's fundamental domain of `N(F)` in
  `N(𝔸)`. Proof: the Library's `subgroupCharacterCoefficient_eq_setIntegral`.
* `haar_unipotentFundamentalDomain_lt_top`: this fundamental domain has finite Haar measure, by
  `LeftCosetSpace.haar_fundamentalDomain_ne_top` and finiteness of the quotient measure.
* `integrableOn_whittakerIntegrand`: if `f` is continuous and bounded on `N(𝔸) g`, the integrand is
  integrable on the fundamental domain. A bounded measurable function on a set of finite measure is
  integrable.
* `whittaker_add`: `W_{f + f'}(g) = W_f(g) + W_{f'}(g)` for continuous left invariant `f`, `f'`
  that are bounded on `N(𝔸) g`. Proof: additivity of the set integral, which applies because both
  integrands are integrable.
* `whittaker_smul`: `W_{c f}(g) = c W_f(g)`, from `integral_const_mul`.
