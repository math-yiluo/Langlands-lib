# Height reduction for the actual adelic `GL(2)`

This module proves reduction theory for the actual adelic group
`AdelicGL F 2 = GL (Fin 2) (AdeleRing (𝓞 F) F)` over an arbitrary number field
`F` in universe `u`: a Hermite-type bound for the minimum of the heights of the
rational vectors under an adelic matrix, and the decomposition of every adelic
matrix, after a rational change of basis, as a bounded matrix times an upper
triangular matrix whose diagonal ideles satisfy `|t₁| ≤ c |t₂|`. All objects are
the actual ones of `Langlands.Global.PrimitiveAdelicHeight`: vectors in
`Fin n → Adeles F` over the full adele ring, maximum coordinate norms at every
place, normalized finite norms, and the archimedean multiplicities `w.mult` in
the height.

## Provenance

The statements are derived. Springer, *Reduction theory over global fields*
(1994), §§1.9–1.10, printed pp.210–211, PDF pp.4–5 (registered as
`springer-1994-reduction-global-fields`, SHA256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`), works over
the base field `k₀ = ℚ` or a rational function field over a finite field. For
`k₀ = ℚ` his height uses maximum norms at the finite places and the Euclidean
length at the infinite place; `M = ∏ M_v` is the compact subgroup of
`GL(2, A)` preserving these norms, every `g` is written `g = m t` with `m ∈ M`
and `t` upper triangular with diagonal ideles `t₁, t₂`, and `T(c)` is the set of
such `t` with `|t₁ / t₂| ≤ c`. Proposition 1.10 states that some `c > 0` gives
`GL(2, A) = M · T(c) · GL(2, k)`. His proof chooses `γ ∈ GL(2, k)` so that
`g γ e₁` has minimal height among the `g γ r`, `r ≠ 0` rational, and deduces
`|t₁| ≤ ‖(λ + μ u) t₁ e₁ + μ t₂ e₂‖` for `λ, μ ∈ k` not both zero; for `k = ℚ`
this gives `c = 2/√3`.

This module differs from that statement and proof as follows.

* The field is an arbitrary number field `F`, and the height uses maximum norms
  at every place, including the infinite ones.
* There is no Iwasawa decomposition and no compact subgroup. The left factor
  `k` is an explicit actual adelic matrix with integral finite entries, infinite
  entries of norm at most `1`, and determinant of local norm `1` at every place.
  It is constructed from the content-normalized first column of `g` and need
  not preserve the local norms. It changes heights by at most the factor
  `2 ^ [F : ℚ]`.
* The Hermite bound `exists_rationalHeight_le_sqrt_det` is an intermediate
  statement of this route, not a statement of Springer's. It combines the
  bounded factor with the project's rank-two height bound
  `exists_rankTwoVector_height_le` (module `PrimitiveAdelicGauss`, itself a
  derived replacement for Springer's choice of coefficients when `k = ℚ`). The
  reduction inequality then follows from the minimality of the first column, as
  in Springer's proof, with the constant `c = C²`, where
  `C = 2 ^ [F : ℚ] · Cst` and `Cst` is the constant of the rank-two bound.

The constants and intermediate lemmas are internal to this route.

## Definitions

* `indicatorAdele F y`, for `y : Vector F 2`, is the actual adele whose
  component at each place (infinite or finite) is `1` if the first coordinate of
  `y` has local norm `1` there and `0` otherwise.
* `completionMatrix F y` is the adelic matrix `!![y 0, 1 - e; y 1, e]` with
  `e = indicatorAdele F y`.
* `firstColumn F g` is `g *ᵥ rational F 2 ![1, 0]`, the first column of
  `g : AdelicGL F 2`, a primitive vector (`firstColumn_isPrimitive`).
* `firstContent F g` is its content idele `contentIdele`, and
  `firstDirection F g` is the normalized vector `normalizedVector`, whose local
  maximum norms are all `1`.
* `boundedFactor F g : AdelicGL F 2` is `completionMatrix F (firstDirection F g)`
  as a unit (`isUnit_completionMatrix`).
* `triangularFactor F g` is `(boundedFactor F g)⁻¹ * g`.
* `secondDiagonal F g` is the idele `det (triangularFactor F g) * (firstContent F g)⁻¹`.

## Results

Heights under bounded matrices:

* `finiteNorm_mulVec_le`: if every entry of an adelic matrix `k` has norm at most
  `1` at a finite place `v`, then `finiteNorm F n (k *ᵥ x) v ≤ finiteNorm F n x v`.
* `infiniteNorm_mulVec_le`: if every entry has norm at most `A ≥ 0` at an
  infinite place `w`, then `infiniteNorm F n (k *ᵥ x) w ≤ (n A) · infiniteNorm F n x w`.
* `height_le_of_local_le`: for primitive `x, y`, finite norms of `x` at most those
  of `y` and infinite norms of `x` at most `M ≥ 0` times those of `y` give
  `height F n x ≤ M ^ [F : ℚ] · height F n y`.
* `height_mulVec_le`: for `k : AdelicGL F n` with all finite entry norms at most
  `1` and all infinite entry norms at most `A ≥ 0`, and primitive `x`,
  `height F n (k *ᵥ x) ≤ (n A) ^ [F : ℚ] · height F n x`.

The completion matrix:

* `finiteProjection_indicatorAdele`, `infiniteProjection_indicatorAdele`: the
  local components of `indicatorAdele F y`.
* `norm_ite_le_one`, `norm_one_sub_ite_le_one`: in a normed field,
  `‖if p then 1 else 0‖ ≤ 1` and `‖1 - if p then 1 else 0‖ ≤ 1`.
* `norm_local_completion_det`: in a normed field, for `z : Fin 2 → K` of maximum
  norm `1` and `e = if ‖z 0‖ = 1 then 1 else 0`, the determinant
  `z 0 * e - (1 - e) * z 1` has norm `1`.
* `completionMatrix_det`: `det (completionMatrix F y) = y 0 * e - (1 - e) * y 1`.
* `norm_finiteProjection_completionMatrix_det`,
  `norm_infiniteProjection_completionMatrix_det`: at a place where `y` has local
  maximum norm `1`, this determinant has local norm `1`.
* `isUnit_of_local_norm`: an adele with finite local norms all `1` and nonzero
  infinite components is a unit of the adele ring.
* `isUnit_completionMatrix`: if `y` has local maximum norm `1` at every place,
  `completionMatrix F y` is invertible.

The decomposition `g = boundedFactor F g * triangularFactor F g`:

* `boundedFactor_val`, `boundedFactor_mul_triangularFactor`.
* `mulVec_rational_first_apply`: `(M *ᵥ rational F 2 ![1, 0]) i = M i 0`.
* `boundedFactor_mulVec_first`: the first column of the bounded factor is
  `firstDirection F g`.
* `triangularFactor_mulVec_first`, `triangularFactor_zero_zero`,
  `triangularFactor_one_zero`: the first column of the triangular factor is
  `firstContent F g` times `(1, 0)`.
* `firstContent_mul_secondDiagonal`, `triangularFactor_one_one`: the
  lower-right entry of the triangular factor is `secondDiagonal F g`.
* `finiteProjection_boundedFactor_le`, `infiniteProjection_boundedFactor_le`:
  every entry of the bounded factor has norm at most `1` at every place.
* `finiteProjection_det_boundedFactor`, `infiniteProjection_det_boundedFactor`,
  `full_det_boundedFactor`: its determinant has local norm `1` at every place,
  hence normalized idele absolute value `IdeleAbsoluteValue.full` equal to `1`.
* `full_det_eq`: `|det g| = |firstContent F g| · |secondDiagonal F g|`.
* `rationalHeight_first`: `rationalHeight F 2 g ![1, 0] = |firstContent F g|`.
* `height_boundedFactor_mulVec_le`: the bounded factor increases heights of
  primitive vectors by at most the factor `2 ^ [F : ℚ]`.
* `triangularFactor_mulVec_rational`: the triangular factor maps
  `rational F 2 ![l, m]` to `t₂ • rankTwoVector F (t₁ t₂⁻¹) (b₀₁ t₂⁻¹) l m`,
  where `t₁ = firstContent F g`, `t₂ = secondDiagonal F g` and `b₀₁` is the
  upper-right entry of the triangular factor.

Main results:

* `exists_rationalHeight_le_sqrt_det` (Hermite bound): there is `C > 0` such that
  every `g : AdelicGL F 2` has a nonzero `r : Fin 2 → F` with
  `rationalHeight F 2 g r ≤ C · √|det g|`, where `|det g|` is
  `IdeleAbsoluteValue.full F (det g)` as a real number.
* `exists_reduction` (`GL(2)` reduction): there is `c > 0` such that every
  `g : AdelicGL F 2` admits `γ : RationalGL F 2`, `k b : AdelicGL F 2` and ideles
  `t₁ t₂` with `g * AdelicGL.rational F 2 γ = k * b`; every entry of `k` has norm
  at most `1` at every finite and every infinite place; `det k` has local norm
  `1` at every finite and every infinite place; `b 0 0 = t₁`, `b 1 0 = 0`,
  `b 1 1 = t₂`; and `|t₁| ≤ c |t₂|` for the normalized idele absolute values.

## Proof

The local norm lemmas are the ultrametric and the triangle inequality for the
sums `∑ⱼ k i j * x j`; `height_le_of_local_le` uses `∑ w, w.mult = [F : ℚ]` for
the infinite product and `finprod_le_finprod₀` for the finite product, which has
finite multiplicative support for primitive vectors.

For the completion, at a place where `‖z‖ = 1` either `‖z 0‖ = 1`, and then
`e = 1` and the determinant is `z 0`, or `‖z 0‖ < 1`, and then `‖z 1‖ = 1`,
`e = 0` and the determinant is `-z 1`. `isUnit_of_local_norm` builds the
inverse at the finite places in the local integers, so the restricted product
condition holds at every place; the matrix is then invertible by
`Matrix.isUnit_iff_isUnit_det`. The first column of `g` is
`firstContent F g • firstDirection F g` (`contentIdele_smul_normalizedVector`),
which gives the first column of `triangularFactor F g`; the determinant formula
for `2 × 2` matrices and cancellation of the unit `firstContent F g` give its
lower-right entry. All entries of the bounded factor are local coordinates of
`firstDirection F g`, `e` or `1 - e`, hence of norm at most `1`, and
`height_mulVec_le` with `n = 2`, `A = 1` gives the factor `2 ^ [F : ℚ]`.
`rationalHeight_first` is `full_contentIdele`.

For the Hermite bound, write `g = k b` as above with diagonal ideles `t₁, t₂`.
`exists_rankTwoVector_height_le` applied to `x = t₁ t₂⁻¹` and `u = b₀₁ t₂⁻¹`
gives `l, m ∈ F`, not both zero, with `height (rankTwoVector …) ≤ Cst √|x|`.
By `triangularFactor_mulVec_rational` and the published scaling law
`IsPrimitive.height_smul`, `height (b r) = |t₂| · height (rankTwoVector …)` for
`r = (l, m)`, so `rationalHeight F 2 g r ≤ 2 ^ [F : ℚ] · |t₂| · Cst · √(|t₁| / |t₂|)
= C √(|t₁| |t₂|) = C √|det g|` by `full_det_eq`.

For the reduction, replace `g` by `h = minimumAdaptedMatrix F 2 g`, that is
`g * AdelicGL.rational F 2 γ` with `γ = minimumBasisChange F 2 g`, and decompose
`h = k b` with `k = boundedFactor F h`, `b = triangularFactor F h`. By
`minimumAdaptedMatrix_first_min` and `rationalHeight_first`,
`|t₁| = rationalHeight F 2 h ![1, 0] ≤ rationalHeight F 2 h r` for every nonzero
rational `r`; the Hermite bound gives such an `r` with height at most
`C √(|t₁| |t₂|)`. Squaring `|t₁| ≤ C √(|t₁| |t₂|)` and dividing by `|t₁| > 0`
gives `|t₁| ≤ C² |t₂|`.

## Scope

Only the actual adelic `GL(2)` statements above are proved. The module does not
assert that the set of possible `k` is compact, nor a maximal-compact Iwasawa
decomposition, nor any statement for `SL(2)`, `GL(n)` with `n > 2`, the
higher-rank induction, the descent to connected reductive groups, or the
general reductive Siegel-cover theorem.
