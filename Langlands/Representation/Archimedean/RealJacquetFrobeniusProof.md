# Proof of `RealJacquetFrobeniusStatement`

Module: `Langlands.Representation.Archimedean.RealJacquetFrobeniusProof` (namespace
`Langlands.Archimedean.RealJacquetFrobenius`).

Main theorem: `Langlands.Archimedean.RealJacquetFrobenius.realJacquetFrobenius :
Langlands.Archimedean.RealJacquetFrobeniusStatement.{uV}`. Like the statement, the theorem has
the single universe parameter `uV`, the universe of the module carrier. It uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## What is proved

`RealJacquetFrobeniusStatement` is stated in
`Langlands.Representation.Archimedean.RealJacquetReduction`. Let `(ρ, π)` be a
`(𝔤𝔩_n(ℝ), O(n))`-module (`IsRealGKModule n ρ π`) on a complex vector space `V`. Let `ℓ ≠ 0`
be a real Jacquet functional with exponents `a : Fin n → ℂ` and signs `e : Fin n → Fin 2`
(`IsRealJacquetFunctional n ρ π ℓ a e`). So `ℓ` kills `π(1 ⊗ X) V` for strictly upper
triangular `X`, `ℓ ∘ π(1 ⊗ E_jj) = a_j ℓ`, and `ℓ ∘ ρ(s_j) = (-1)^{e_j} ℓ` for the sign
reflections `s_j`. The statement asks for real characters `c_0, …, c_{n-1}` with parity `e_j`
and exponent `t_j` such that `t_j + (n - 1)/2 - j = a_j`. It also asks for a nonzero linear
map `B` from `V` into the `O(n)`-finite functions of `realStandardModule n` of these
characters that is an intertwining map (`IsRealStandardEmbedding`): `B(ρ(k) v) = R(k)(B v)`
for `k ∈ O(n)` and `B(π(1 ⊗ X) v) = R(X)(B v)` for real matrices `X`. Here `R` denotes right
translation and the right derivative `rightDerivative (matrixModel ℝ n) X`.

The proof follows Frobenius reciprocity (Wallach 1979, 4.16–4.17, in the Library's
right-translation convention, as explained in the statement module's Markdown). Write
`χ(b) = ∏ⱼ sgn(b_jj)^{e_j} |b_jj|^{a_j}` for an invertible upper triangular matrix `b`. Then

`B v (b k) = χ(b) ℓ(ρ(k) v)`   (`b` invertible upper triangular, `k ∈ O(n)`).

The characters are `c_j = sgn^{e_j} |·|^{t_j}` with `t_j = a_j - (n - 1)/2 + j` (`chars`,
`expo`). The identity `t_j + (n - 1)/2 - j = a_j` is a ring computation.

## Proof route

### Characters (section `Character`)

- `charFun e t x = (x/|x|)^e · |x|^t` on `ℝ`. It is multiplicative (`charFun_mul`), nonzero
  on `ℝˣ` (`charFun_ne_zero`) and smooth away from `0` (`contDiffAt_charFun`). The power
  `|x|^t` is smooth at `|x| > 0` because complex `z ↦ z^t` is analytic on the slit plane.
- `charHom e t : ℝˣ →ₜ* ℂˣ` and `charData e t : RealCharacterData`, with parity `e`,
  exponent `t`, and `character_eq` holding by `rfl`.
- `realPositionCharacter_map_character`: for a list of character blocks, the `i`-th position
  character is the `i`-th character (induction on the list).
- `charFun_mul_cpow`: `charFun e t x · |x|^s = charFun e (t + s) x` for `x ≠ 0`.

### The character `χ` (section `Diag`)

- `diagChar a e M = ∏ⱼ charFun (e j) (a j) (M j j)`. This is `χ` evaluated through the
  diagonal of `M`.
- `diagChar_mul`: for upper triangular `A` and `C`, `(A C)_jj = A_jj C_jj`
  (`upper_mul_apply_self`), so `χ(A C) = χ(A) χ(C)`.
- `diagChar_of_diag_eq_one`: `χ = 1` on matrices with unit diagonal (upper unipotent
  matrices).
- `diag_ne_zero`: an invertible upper triangular matrix has nonzero diagonal entries, because
  its determinant is the product of the diagonal.
- `contDiffAt_diagChar`: `χ` is smooth at every matrix with nonzero diagonal.
- `charFun_exp`: `charFun e t (exp x) = exp(x t)`.

### Well-definedness on `B ∩ O(n)` (section `Signs`)

- `upper_orthogonal`: an upper triangular orthogonal matrix `m` is diagonal with entries `±1`.
  Its inverse `mᵀ` is upper triangular as the inverse of an upper triangular matrix, so `m` is
  also lower triangular. The diagonal entries satisfy `m_jj² = 1` by `mᵀm = 1`.
- `signDiag S` is the diagonal sign matrix with `-1` exactly on `S`. It is the product of the
  `s_j` for `j ∈ S` (`signDiag_insert`). So `ℓ(ρ(signDiag S) w) = ∏_{j ∈ S} (-1)^{e_j} ℓ(w)`
  (`apply_signDiag`, induction on `S` using the sign clause of `IsRealJacquetFunctional`).
- `apply_upper_orthogonal`: for upper triangular `m ∈ O(n)`, `ℓ(ρ(m) w) = χ(m) ℓ(w)`.

### The Frobenius function (section `Iwasawa`)

- The Library's `exists_upperTriangular_mul_unitary` (`TriangularUnitary`) gives for every
  `g ∈ GL_n(ℝ)` a decomposition `g = b k` with `b` invertible upper triangular and
  `k ∈ O(n)`. `iwB g`, `iwK g` and `iwKU g` are a chosen such decomposition.
- `frobFun ρ ℓ a e v g = χ(iwB g) · ℓ(ρ(iwKU g) v)`.
- `frobFun_eq`: for **every** decomposition `g = b k` of this kind,
  `frobFun v g = χ(b) ℓ(ρ(k) v)`. Indeed `m = iwK g · kᵀ = (iwB g)⁻¹ b` is upper triangular and
  orthogonal. So `ℓ(ρ(iwK g) v) = ℓ(ρ(m) ρ(k) v) = χ(m) ℓ(ρ(k) v)`, and
  `χ(iwB g) χ(m) = χ(b)` by `diagChar_mul`.

### Left equivariance (section `Equivariance`)

- `posChar_apply`: the position characters of `chars a e` are `charFun (e j) (expo a j)`.
- `principalSeriesCharacter_eq`: the Library's `principalSeriesCharacter` of these characters
  at `diag(d)` is `∏ⱼ charFun (e j) (t_j) (d_j) |d_j|^{(n-1)/2 - j}`. By `charFun_mul_cpow`
  this is `∏ⱼ charFun (e j) (a j) (d_j) = χ(diag(d))`.
- `frobFun_left`: for `g = b k`, `diag(d) u g = (diag(d) u b) k`. So, by `frobFun_eq` and
  multiplicativity of `χ` (with `χ(u) = 1`),
  `B v (diag(d) u g) = principalSeriesCharacter(d) · B v (g)`. This is the transformation law
  of `principalSeries` (`mem_principalSeries_iff`).

### Linearity and `O(n)` (section `Linear`)

- `frobLin : V →ₗ[ℂ] (GL_n(ℝ) → ℂ)`, `v ↦ frobFun v`.
- `frobFun_rightTranslation`: `B(ρ(k) v) = R(k)(B v)` for `k ∈ O(n)`. With
  `g = iwB g · iwK g`, the matrix `g k` decomposes as `iwB g · (iwK g · k)`. Apply
  `frobFun_eq` and `ρ(iwK g) ρ(k) = ρ(iwK g · k)`.
- `frobFun_mem_kFiniteVectors`: the right `O(n)`-translates of `B v` are the images under
  `frobLin` of the vectors `ρ(k) v`. These lie in the finite-dimensional span of the
  `ρ`-orbit of `v` (the first clause of `IsRealGKModule`), so `B v` is `O(n)`-finite.

### Local smooth Iwasawa coordinates (section `Split`)

Each real matrix `M` splits uniquely as `M = U(M) + S(M)` with `U(M)` upper triangular
(`upperPart`) and `S(M)` antisymmetric (`skewPart`; `S(M)_ij = M_ij` for `j < i`). For an
invertible upper triangular `b₀`, the smooth map

`iwMap b₀ M = (b₀ + U(M)) · exp(S(M))`

has derivative `M ↦ U(M) + b₀ S(M)` at `0` (`hasFDerivAt_iwMap`). This derivative is
injective (`iwDeriv_injective`): if `U + b₀ S = 0`, then `S = -b₀⁻¹ U` is upper triangular and
antisymmetric, hence `0` (`eq_zero_of_skew_of_upper`), and then `U = 0`. So it is a linear
isomorphism (`iwDerivEquiv`). Mathlib's inverse function theorem
(`ContDiffAt.localInverse`) gives `exists_localIwasawa`: a map `Ψ`, smooth at `b₀`, with
`Ψ b₀ = 0` and `iwMap b₀ (Ψ y) = y` for `y` near `b₀`.

### Smoothness (section `Smooth`)

- `polyEval P m` evaluates a complex polynomial `P` in the entries of a real matrix `m`. It is
  smooth (`contDiff_polyEval`, induction on `P`).
- `exists_polyEval`: for `v ∈ V`, the function `k ↦ ℓ(ρ(k) v)` on `O(n)` is the restriction
  of some `polyEval P`. Its right translates are the functions `k ↦ ℓ(ρ(k) ρ(k') v)`, which
  span a finite-dimensional space (`O(n)`-finiteness), and it is continuous (second clause of
  `IsRealGKModule`). The Library's
  `OrthogonalFinitePolynomial.exists_mvPolynomial_of_finiteDimensional_span` gives `P`.
- `contDiffAt_unitsExtension_frobFun`: the extension of `B v` by `0` off the invertible
  matrices (`unitsExtension`, Library module `PrincipalSeriesStability`) is smooth at every
  invertible `y₀`. Write `y₀ = b₀ k₀` with `b₀ = iwB y₀` and `k₀ = iwK y₀`, and take `Ψ` for
  `b₀`. For invertible `y` near `y₀`,

  `y = (b₀ + U(Ψ(y k₀ᵀ))) · (exp(S(Ψ(y k₀ᵀ))) k₀)`,

  where the first factor is upper triangular and the second lies in `O(n)` (the exponential of
  an antisymmetric matrix is orthogonal). By `frobFun_eq` and `exists_polyEval`, near `y₀`

  `B v (y) = χ(b₀ + U(Ψ(y k₀ᵀ))) · P(exp(S(Ψ(y k₀ᵀ))) k₀)`.

  Here `χ` is smooth near `b₀`, because the diagonal of `b₀` is nonzero, and the rest is a
  composition of smooth maps.
- `contMDiff_frobFun`: `B v` is smooth on the manifold `GL_n(ℝ)`. This follows from the
  previous item by the Library's `contMDiff_of_contDiffOn`.

### Right derivatives (section `RightDerivative`)

- `jacquet_upper`: for upper triangular `U`, `ℓ(π(1 ⊗ U) w) = (∑ⱼ a_j U_jj) ℓ(w)`. Write
  `U = N + ∑ⱼ U_jj E_jj` with `N` strictly upper triangular. The map `M ↦ ℓ(π(1 ⊗ M) w)` is
  real linear (`actFun`). `ℓ` kills the `N` term, and `E_jj` contributes `a_j ℓ(w)`.
- `diagChar_exp_diagonal`: `χ(exp(diag x)) = exp(∑ⱼ x_j a_j)`. This uses the Library's
  `RealPrincipalSeriesDuality.matrixExpUnit_diagonal` and `charFun_exp`.
- `frobFun_rightDerivative`: `B(π(1 ⊗ X) v)(g) = R(X)(B v)(g)`. Let `g = b k` with `b = iwB g`
  and `k = iwK g`, and put `w = ρ(k) v` and `Y = k X kᵀ = U + Z`, where `U = U(Y)` is upper
  triangular and `Z = S(Y)` is antisymmetric. Split `U = Δ + N` into its diagonal `Δ` and
  strictly upper part `N`, and put `s = ∑ⱼ a_j U_jj`.
  - Left side: the fourth clause of `IsRealGKModule` gives `ρ(k) π(1 ⊗ X) v = π(1 ⊗ Y) w`. By
    `frobFun_eq` and `jacquet_upper`, the left side is `χ(b) (s ℓ(w) + ℓ(π(1 ⊗ Z) w))`.
  - Right side: by the Library's `rightDerivative_eq_fderiv`, it is the derivative of the
    extension of `B v` at `g` in the direction `g X`. Consider the curve
    `Γ(t) = b · exp(tΔ) · (1 + tN) · (exp(tZ) k)`. Then `Γ(0) = g`. Its velocity at `0` is
    `b(Δ + N + Z) k = b Y k = g X`. The velocity is computed with the Library's
    `RealPrincipalSeriesDuality.hasDerivAt_exp_smul_zero` and the product rule. Each `Γ(t)`
    is invertible, and `b exp(tΔ)(1 + tN)` is upper triangular while `exp(tZ) k ∈ O(n)`. So by
    `frobFun_eq`, `diagChar_exp_diagonal` and `χ(1 + tN) = 1`,

    `B v (Γ(t)) = χ(b) · exp(t s) · ℓ(ρ(exp(tZ)) w)`.

    By the chain rule, the derivative of the extension of `B v` at `g` in the direction `g X`
    is the derivative of this function at `t = 0`. The third clause of `IsRealGKModule`
    (along the curve `t ↦ exp(tZ)` in `O(n)`, whose entries have derivative `Z` at `0`) and
    the product rule give `χ(b) (s ℓ(w) + ℓ(π(1 ⊗ Z) w))`. Uniqueness of derivatives
    (`HasDerivAt.unique`) identifies the two sides.

### Assembly (section `Assembly`)

- The imported `RealPrincipalSeriesDuality.realInducedBlockAt_map_character` shows that a
  list of character blocks has no induction blocks. So
  membership in `realStandardModule` reduces to membership in `principalSeries`; the Fourier
  vanishing condition is vacuous.
- `realJacquetFrobenius`: take `c = chars a e`. Each `B v` lies in
  `kFiniteFunctions (realStandardModule n …) (unitaryCompact ℝ n)`. This uses
  `contMDiff_frobFun` and `frobFun_left` (principal series), the previous item (standard
  module) and `frobFun_mem_kFiniteVectors` (`O(n)`-finiteness). So `frobLin` restricts to a
  linear map `B` into this space. It is nonzero: `B v (1) = χ(1) ℓ(ρ(1) v) = ℓ(v)` by
  `frobFun_eq` with `b = k = 1`, so `B = 0` would force `ℓ = 0`. The two clauses of
  `IsRealStandardEmbedding` are `frobFun_rightTranslation` and `frobFun_rightDerivative`.

## Library results used

- `RealJacquetReduction`: `realJacquetSubspace`, `signReflection`, `IsRealJacquetFunctional`,
  `RealJacquetFrobeniusStatement`.
- `GKModule`: `IsRealGKModule`. `RealPrincipalSeriesQuotientReduction`:
  `IsRealStandardEmbedding`. `StandardModule`: `principalSeries`, `mem_principalSeries_iff`,
  `principalSeriesCharacter`, `realStandardModule`, `realPositionCharacter`,
  `realInducedBlockAt`, `kFiniteFunctions`, `rightDerivative`.
- `TriangularUnitary`: `exists_upperTriangular_mul_unitary`, `IsTriangularUnitaryFactorization`.
- `PrincipalSeriesStability`: `unitsExtension`, `unitsExtension_val`,
  `isOpen_setOf_isUnit_matrix`, `differentiableAt_unitsExtension`, `contMDiff_of_contDiffOn`,
  `rightDerivative_eq_fderiv`.
- `OrthogonalFinitePolynomial`: `exists_mvPolynomial_of_finiteDimensional_span`.
- `RealStandardModuleFourier`: `matrixExpUnit`, `matrixExpUnit_val`.
- `RealPrincipalSeriesDualityProof`: `hasDerivAt_exp_smul_zero`, `hasDerivAt_entry`,
  `unipotentLine`, `isUpperTriangular_one_add_smul`, `matrixExpUnit_diagonal`,
  `ofReal_exp_cpow`.

## References

- N. R. Wallach, *Representations of reductive Lie groups*, in Automorphic Forms,
  Representations and L-Functions (Corvallis, 1977), Proc. Sympos. Pure Math. 33, part 1,
  AMS, 1979, pp. 71–86. Used: 4.16–4.17 (Frobenius reciprocity), as cited by the statement.
  Library source ID `wallach-1979-representations-reductive-lie-groups`. The analytic details
  (the well-definedness check on `B ∩ O(n)`, smoothness through polynomial `O(n)`-finite
  matrix coefficients and local Iwasawa coordinates, and the curve computation of right
  derivatives) are this proof's own route.
