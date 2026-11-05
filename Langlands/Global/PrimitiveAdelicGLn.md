# Height reduction for the actual adelic `GL(n)`

This module proves reduction theory for the actual adelic group
`AdelicGL F n = GL (Fin n) (AdeleRing (𝓞 F) F)` over an arbitrary number field
`F` in universe `u`, for every `n : ℕ` (including `n = 0` and `n = 1`). After right
multiplication by a rational invertible matrix, every adelic matrix is a bounded
matrix with unit local determinants times an upper triangular matrix whose
consecutive diagonal ideles satisfy `|tᵢ| ≤ c |tᵢ₊₁|`. All objects are the actual
ones of `Langlands.Global.PrimitiveAdelicHeight`: vectors in `Fin n → Adeles F`
over the full adele ring, maximum coordinate norms at every place, normalized
finite norms, the archimedean multiplicities `w.mult` in the height, and the
normalized idele absolute value `IdeleAbsoluteValue.full`.

## Provenance

The statements are derived. Springer, *Reduction theory over global fields*
(1994), registered as `springer-1994-reduction-global-fields`, SHA256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, treats
`GL(2)` in §§1.9–1.10 (printed pp.210–211, PDF pp.4–5) and connected reductive
groups in §2 (printed pp.211–213, PDF pp.5–7). He does not state a separate
`GL(n)` theorem.

* Proposition 1.10 states `GL(2, A) = M · T(c) · GL(2, k)` for `k = ℚ` or a
  rational function field. Here `M` is the compact subgroup preserving the local
  norms, and `T(c)` is the set of upper triangular `t` with diagonal ideles
  `t₁, t₂` and `|t₁ / t₂| ≤ c`. His proof chooses `γ` so that `g γ e₁` has minimal
  height and deduces `|t₁| ≤ ‖(λ + μ u) t₁ e₁ + μ t₂ e₂‖`.
* In §2.3 (printed p.212) he fixes representations `(ρᵢ, Vᵢ, ξᵢ)` adapted to the
  parabolic subgroups `Pᵢ` and heights `‖ ‖ᵢ` on `Vᵢ(A)`, and defines, for
  `c > 0`, the set `𝓡(c)` of `g ∈ G(A)⁰` with
  `‖ρᵢ(g) ξᵢ‖ᵢ ≤ c ‖ρᵢ(gγ) ξᵢ‖ᵢ` for `i ∈ [1, r]` and `γ ∈ Pᵢ(k)`. As printed,
  `γ` ranges over `Pᵢ(k)`, not over all of `G(k)`. He then states that property
  (d) of heights gives `G(A)⁰ = 𝓡(1) · G(k)`. Lemma 2.4 (printed pp.212–213) is
  introduced as "a reduction to rank one, following [5, 9.3]". Assuming (F) for
  the Levi groups `Lᵢ` (`1 ≤ i ≤ r - 1`), part (i) gives `c'` with
  `𝓡(c) ⊂ 𝒮(c')`. The proof is by induction on the rank: the Levi group `L₁` of
  smaller rank bounds the simple-root values `|αᵢ(s)|` for `i > 1`, and "a
  similar argument, using the rank one group `L_{r-1}`" bounds `|α₁(s)|`.

This module uses neither the set `𝓡(c)` nor Lemma 2.4 as stated. Lemma 2.4 is
only a conceptual model for the rank induction below. The minimality condition
actually used is the `GL(2)` one from the proof of Proposition 1.10, carried
over to the first column in rank `n`.

The route in detail:

* The field is an arbitrary number field and the height uses maximum norms at
  every place, including the infinite ones.
* Only the first column is minimized: `γ` is chosen by `minimumBasisChange`
  (module `PrimitiveAdelicBasis`) so that the height of the first column of
  `g γ` is at most the height of `g v` for every nonzero rational vector `v`.
  This is the minimal-height choice in the proof of Proposition 1.10, taken over
  all rational vectors in rank `n`. It is not Springer's `𝓡(1)` condition for
  `i = 1`, which quantifies only over `γ ∈ P₁(k)`. Other exterior powers are not
  used.
* There is no Iwasawa decomposition and no compact subgroup. The left factor is
  an explicit adelic matrix completing the content-normalized first column.
  Locally it is a permutation of a matrix whose other columns are standard basis
  vectors. It has integral finite entries, bounded infinite entries, and
  determinant of local norm `1` at every place. It need not preserve the local
  norms.
* The induction runs on the lower right block of size `n - 1` (Levi
  `GL(1) × GL(n - 1)`). The first diagonal ratio comes from the project's
  `GL(2)` Hermite bound `exists_rationalHeight_le_sqrt_det` (module
  `PrimitiveAdelicGL2`, itself derived), applied to the upper left `2 × 2`
  block. This plays the role of Springer's rank-one step.

The constants, the column completion and all intermediate lemmas are internal to
this route.

## Definitions

Local and block constructions (for a normed field `K` or a commutative ring `R`):

* `maxIndex z`, for `z : Fin (p + 1) → K`, is a chosen index where `‖z i‖` is
  maximal.
* `firstColumnMatrix w` is the matrix whose first column is `w` and whose
  column `c ≠ 0` is the standard basis vector `e_c`.
* `localCompletion z` is `firstColumnMatrix (z ∘ σ)` with its rows permuted by
  `σ`, where `σ = Equiv.swap 0 (maxIndex z)`. Its first column is `z`.
* `lowerBlock M` is the lower right `p × p` block of a `(p + 1) × (p + 1)` matrix.
* `extendMatrix A` is the block diagonal matrix `diag(1, A)`. `extendHom R p` is
  the corresponding monoid homomorphism of matrix monoids, and `extendGL R p` is
  the induced homomorphism `GL (Fin p) R →* GL (Fin (p + 1)) R`.

Adelic objects:

* `IsBoundedUnimodular F n B k`, for `k : AdelicGL F n`: every entry of `k` has
  norm at most `1` at every finite place and at most `B` at every infinite place,
  and `det k` has local norm `1` at every finite and every infinite place.
* `IsReducedTriangular F n c b`, for `b : AdelicGL F n`: `b` is upper triangular,
  and there are ideles `t : Fin n → Ideles F` with `b i i = t i` and
  `|t i| ≤ c · |t j|` whenever `i.val + 1 = j.val`. Here `|·|` is
  `IdeleAbsoluteValue.full F` as a real number.
* `HasReduction F n c B`: every `g : AdelicGL F n` admits `γ : RationalGL F n` and
  `k b : AdelicGL F n` with `g * AdelicGL.rational F n γ = k * b`,
  `IsBoundedUnimodular F n B k` and `IsReducedTriangular F n c b`.
* `columnCompletion F y`, for `y : Vector F (p + 1)`, is the adelic matrix whose
  component at every infinite and every finite place is the `localCompletion` of
  the local components of `y`. Its entries are entries of `y`, `0` or `1`.
* For `g : AdelicGL F (p + 1)`:
  * `leadingColumn g = g *ᵥ rational F (p + 1) (firstVector …)` is the first
    column.
  * `leadingContent g` is its content idele and `leadingDirection g` its
    normalized vector.
  * `leadingFactor g` is `columnCompletion F (leadingDirection g)` as a unit.
  * `leadingRemainder g = (leadingFactor g)⁻¹ * g`.
  * `lowerRemainder g : AdelicGL F p` is the lower right block of
    `leadingRemainder g`, as a unit.
* `padRational r` and `padVector x` extend a rational, respectively adelic,
  vector of length `2` by zeros to length `p + 2`. `upperBlockTwo b` is the upper
  left `2 × 2` block.
* `stepTriangular h k' γ' = diag(1, k'⁻¹) · leadingRemainder h · diag(1, γ')` and
  `stepBounded h k' = leadingFactor h · diag(1, k')` are the two factors of the
  inductive step. Here `diag(1, ·)` is `extendGL`, and `γ'` enters through
  `AdelicGL.rational`.

## Results

Local completion and block lemmas:

* `norm_le_norm_maxIndex`, `norm_maxIndex`: `‖z i‖ ≤ ‖z (maxIndex z)‖` and
  `‖z (maxIndex z)‖ = ‖z‖`.
* `det_firstColumnMatrix`: `det (firstColumnMatrix w) = w 0`.
* `localCompletion_apply`, `localCompletion_zero`: entry formula, and the first
  column is `z`.
* `det_localCompletion`: the determinant is `sign σ · z (maxIndex z)`.
  `norm_det_localCompletion`: its norm is `‖z‖`.
* `norm_localCompletion_le`: if `‖z‖ ≤ 1`, every entry has norm at most `1`.
* `extendMatrix_zero_zero`, `extendMatrix_zero_succ`, `extendMatrix_succ_zero`,
  `extendMatrix_succ_succ`, `lowerBlock_extendMatrix`: entries and lower block of
  `diag(1, A)`.
* `det_eq_mul_det_lowerBlock`: if the first column of `M` vanishes below the
  diagonal, `det M = M 0 0 · det (lowerBlock M)`.
* `lowerBlock_mul`: under the same condition on `M`,
  `lowerBlock (M N) = lowerBlock M · lowerBlock N`.
* `mul_succ_zero`: under the same condition on `M` and `N`, it also holds for `M N`.
* `extendMatrix_mul`, `extendMatrix_one`, `det_extendMatrix`,
  `extendMatrix_mulVec_single`, `map_extendMatrix`, `extendGL_val`: `diag(1, ·)`
  is multiplicative, unital and determinant preserving. It fixes `e₀` and
  commutes with ring homomorphisms applied entrywise.

Entry bounds, for a ring homomorphism `f` to a normed field:

* `norm_map_mul_apply_le_one`: in an ultrametric field, products of matrices
  with entries of norm at most `1` have entries of norm at most `1`.
* `norm_map_mul_apply_le`: if the entries of `A` have norm at most `a ≥ 0` and
  those of `B` at most `b`, the entries of `A B` have norm at most `n · (a · b)`.
* `norm_map_extendMatrix_le`: the entries of `diag(1, A)` are bounded by any
  `B ≥ 1` bounding those of `A`. `norm_map_one_le`: the entries of `1` have norm
  at most `1`.

Bounded unimodular factors:

* `isBoundedUnimodular_one`: `IsBoundedUnimodular F n 1 1`.
* `IsBoundedUnimodular.mul_extendGL`: if `k₁` is bounded unimodular with bound
  `1` in rank `p + 1` and `k'` with bound `B ≥ 1` in rank `p`, then
  `k₁ · diag(1, k')` is bounded unimodular with bound `(p + 1) · B`.

The column completion and the leading decomposition:

* `finiteProjection_columnCompletion`, `infiniteProjection_columnCompletion`,
  `columnCompletion_zero`, `finiteProjection_det_columnCompletion`,
  `infiniteProjection_det_columnCompletion`: local components, first column and
  local determinants of `columnCompletion F y`.
* `isUnit_columnCompletion`: if `y` has local maximum norm `1` at every finite and
  every infinite place, `columnCompletion F y` is invertible.
* `rational_firstVector`: `rational F (p + 1) (firstVector …) = Pi.single 0 1`.
* `leadingColumn_isPrimitive`, `leadingFactor_val`,
  `leadingFactor_mul_leadingRemainder` (`g = leadingFactor g · leadingRemainder g`),
  and `leadingFactor_mulVec_first` (the first column of the factor is
  `leadingDirection g`).
* `leadingRemainder_mulVec_first`, `leadingRemainder_zero_zero`,
  `leadingRemainder_succ_zero`: the first column of `leadingRemainder g` is
  `leadingContent g` times `e₀`.
* `isUnit_lowerBlock_leadingRemainder`, `lowerRemainder_val`: its lower right
  block is invertible.
* `rationalHeight_leading`: the height of the first column of `g` is
  `|leadingContent g|`.
* `isBoundedUnimodular_leadingFactor`:
  `IsBoundedUnimodular F (p + 1) 1 (leadingFactor g)`.

The rank-two step:

* `padRational_ne_zero`, `rational_padRational`, `norm_vecCons_vecCons_zero`,
  `norm_map_padVector`, `height_padVector` (padding by zeros preserves heights),
  and `mulVec_padVector` (if the first two columns of `b` vanish below row `1`,
  then `b` maps `padVector x` to `padVector (upperBlockTwo b *ᵥ x)`).
* `exists_rationalHeight_le_of_triangular`. Assume a `GL(2)` Hermite bound: every
  `g : AdelicGL F 2` has some nonzero `r` with
  `rationalHeight F 2 g r ≤ C · √|det g|`. Let `k` be bounded unimodular with
  bound `B ≥ 0` in rank `p + 2`, and let `b` be upper triangular with
  `b 0 0 = t₀` and `b 1 1 = t₁`. Then some nonzero rational `v` has
  `rationalHeight F (p + 2) (k * b) v ≤ ((p + 2) B) ^ [F : ℚ] · (C · √(|t₀| |t₁|))`.

The inductive step:

* `rational_extendGL`: `diag(1, ·)` commutes with `AdelicGL.rational`.
* `stepBounded_mul_stepTriangular`:
  `stepBounded h k' · stepTriangular h k' γ' = h · AdelicGL.rational (diag(1, γ'))`.
* `stepTriangular_mulVec_first`, `stepTriangular_zero_zero`,
  `stepTriangular_succ_zero`: the first column of `stepTriangular h k' γ'` is
  `leadingContent h` times `e₀`.
* `lowerBlock_stepTriangular`: if
  `lowerRemainder h · AdelicGL.rational γ' = k' · b'`, the lower right block of
  `stepTriangular h k' γ'` is `b'`.
* `isUpperTriangular_stepTriangular`: if moreover `b'` is upper triangular, so is
  `stepTriangular h k' γ'`.
* `first_ratio_le`. Assume the `GL(2)` Hermite bound with constant `C`, and that
  the first column of `h : AdelicGL F (p + 2)` has minimal height among all
  nonzero rational vectors. Assume `lowerRemainder h · AdelicGL.rational γ' = k' · b'`
  with `b'` upper triangular and `b' 0 0 = t₁`, and that `stepBounded h k'` is
  bounded unimodular with bound `B ≥ 0`. Then
  `|leadingContent h| ≤ (((p + 2) B) ^ [F : ℚ] · C) ^ 2 · |t₁|`.

Main results:

* `hasReduction_zero`: `HasReduction F 0 1 1`. `hasReduction_one`:
  `HasReduction F 1 1 1`.
* `hasReduction_succ`: if `HasReduction F (p + 1) c B` with `c > 0` and `B ≥ 1`,
  then `HasReduction F (p + 2) c' B'` for some `c' > 0` and `B' ≥ 1`.
* `exists_hasReduction`: for every `n` there are `c > 0` and `B ≥ 1` with
  `HasReduction F n c B`.
* `exists_reduction_GL` (`GL(n)` reduction): for every `n : ℕ` there are `c > 0`
  and `B ≥ 1` such that every `g : AdelicGL F n` admits `γ : RationalGL F n` and
  `k b : AdelicGL F n` with `g * AdelicGL.rational F n γ = k * b`,
  `IsBoundedUnimodular F n B k` and `IsReducedTriangular F n c b`.

## Proof

Locally, `firstColumnMatrix w` is lower triangular with diagonal `w 0, 1, …, 1`,
so its determinant is `w 0`. Permuting rows by the transposition `σ` multiplies
the determinant by `sign σ = ±1`. Hence `det (localCompletion z)` has norm
`‖z (maxIndex z)‖ = ‖z‖`. For the normalized direction `y = leadingDirection g`
this norm is `1` at every place (`finiteNorm_normalizedVector`,
`infiniteNorm_normalizedVector`). `isUnit_of_local_norm` (module
`PrimitiveAdelicGL2`) then makes `det (columnCompletion F y)` a unit of the adele
ring. The restricted product condition for `columnCompletion F y` holds because
almost all local components of each `y i` are integral. All entries are local
coordinates of `y`, `0` or `1`, hence of norm at most `1`, which gives
`isBoundedUnimodular_leadingFactor`. The first column of `g` is
`leadingContent g • leadingDirection g` (`contentIdele_smul_normalizedVector`).
Hence the first column of `leadingRemainder g` is `leadingContent g • e₀`, and
`det_eq_mul_det_lowerBlock` makes its lower block invertible.
`rationalHeight_leading` is `full_contentIdele`.

For bounded unimodular factors, the finite entry bound of `k₁ · diag(1, k')` uses
the ultrametric inequality. The infinite bound `(p + 1) · (1 · B)` uses the
triangle inequality. The determinant is `det k₁ · det k'` by `det_extendMatrix`.

For the rank-two step, the upper left block `b₂` of the upper triangular `b` has
determinant `t₀ t₁`, so it is invertible. The Hermite bound gives a nonzero `r`
with `rationalHeight F 2 b₂ r ≤ C √(|t₀| |t₁|)`. Since the first two columns of
`b` vanish below row `1`, `b` maps `rational (padRational r)` to the padding of
`b₂ *ᵥ rational r`, and padding preserves heights. `height_mulVec_le` (module
`PrimitiveAdelicGL2`) with `n = p + 2` and `A = B` gives the factor
`((p + 2) B) ^ [F : ℚ]` for `k`.

The ranks `0` and `1` take `γ = 1`, `k = 1` and `b = g`. In rank `1` the single
diagonal idele is `det g`, and there is no ratio condition. For the step from
rank `p + 1` to `p + 2`:

1. Replace `g` by `h = minimumAdaptedMatrix F (p + 2) g`, that is
   `g · AdelicGL.rational γ₀` with `γ₀ = minimumBasisChange F (p + 2) g`
   (module `PrimitiveAdelicBasis`). The first column of `h` has minimal height
   (`minimumAdaptedMatrix_first_min`).
2. Apply the hypothesis to `lowerRemainder h`. This gives `γ'`, `k'` and `b'`
   with `lowerRemainder h · AdelicGL.rational γ' = k' · b'`, together with
   diagonal ideles `t'`.
3. By `stepBounded_mul_stepTriangular`,
   `h · AdelicGL.rational (diag(1, γ')) = stepBounded h k' · stepTriangular h k' γ'`.
   Hence `g · AdelicGL.rational (γ₀ · diag(1, γ'))` has this factorization.
4. `stepBounded h k'` is bounded unimodular with bound `B' = (p + 2) B` by
   `IsBoundedUnimodular.mul_extendGL`.
5. `stepTriangular h k' γ'` is upper triangular with diagonal ideles
   `vecCons (leadingContent h) t'`, by `stepTriangular_zero_zero` and
   `lowerBlock_stepTriangular`.
6. Ratios between consecutive entries of `t'` are bounded by `c`.
7. For the first ratio, `first_ratio_le` combines minimality with the rank-two
   step applied to `stepBounded h k' · stepTriangular h k' γ'`. A vector of this
   product corresponds to a nonzero rational vector for `h` through
   `rationalHeight_mul_rational` and `rational_mulVec_ne_zero`. Write
   `a = |leadingContent h|` and `d = |t'₀|`. Then
   `a ≤ C' √(a d)` with `C' = ((p + 2) B') ^ [F : ℚ] · C`. Squaring and
   dividing by `a > 0` gives `a ≤ C'² d`.

The new constants are `c' = max c C'²` and `B' = (p + 2) B`. The constant `C` is
that of `exists_rationalHeight_le_sqrt_det`. Starting from `B = 1` in rank `1`,
the induction gives `B = n!` in rank `n ≥ 1`. `exists_hasReduction` is the
induction on `n`, and `exists_reduction_GL` unfolds `HasReduction`.

## Scope

Only the actual adelic `GL(n)` statements above are proved. The module does not
assert:

* that the set of possible `k` is compact;
* any maximal-compact (orthogonal or unitary) Iwasawa decomposition at the
  infinite places;
* any reduction of the upper triangular factor's unipotent part modulo rational
  points;
* any statement for `SL(n)`, other classical groups or parabolic subgroups
  other than the upper triangular one;
* the descent to connected reductive groups or the general reductive
  Siegel-cover theorem.
