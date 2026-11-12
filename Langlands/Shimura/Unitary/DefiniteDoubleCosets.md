# Finiteness of definite double cosets for lattice stabilizers

Author: Worker 19.

Let `σ` be an involution of a finite-dimensional `ℚ`-algebra `A` whose real
scalar extension is positive (`(σ.baseChange ℝ).IsPositive`), `GJ` its
similitude group, and `b` a `ℚ`-basis of `A` indexed by `Fin n`. Let
`𝔸_f` be the finite adeles of `ℚ`, `Ẑ ⊆ 𝔸_f` the integral finite adeles and
`ϕ : ℚ → 𝔸_f` the diagonal embedding. The lattice level `K₀ = latticeLevel σ b`
is the stabilizer in `GJ(𝔸_f)` of the lattice `⊕ Ẑ (1 ⊗ b_i)` of
`𝔸_f ⊗ A`, with multiplier in `Ẑ^×`. The main result is

`finite_doubleCosets_latticeLevel`: the double coset space
`GJ(ℚ) \ GJ(𝔸_f) / K₀` is finite,

stated as `Finite (EquivariantForms.DoubleCosets σ.finiteAdelicDiagonal
(latticeLevel σ b))`. The published module `DefiniteFormsTowerLimit` takes the
instance `Finite (DoubleCosets σ.finiteAdelicDiagonal K)` as a hypothesis.
This module proves that instance for the levels `K = K₀`. Arbitrary compact
open levels are not treated here.

## Source

Harris (1999), Section 1, printed p. 301, assumes that the unitary group is
definite, `J_∞ = ∏ U(n)`. Section 3, printed pp. 306–308, writes the definite
forms as functions on the finite set `GJ(ℚ) \ GJ(𝔸_f) / K` (the decomposition
(3.9)), which presupposes this finiteness. The published
`SecondKindInvolution.isPositive_of_hasDefiniteSignature` derives the
positivity hypothesis used here from Harris's definite signature.

The proof is derived. It is the classical reduction-theory argument
(Hermite reduction of integral positive definite forms together with class
number one of `ℚ`), written for this module, and it is not taken from Harris.
The Hermite bound used is Platonov–Rapinchuk, Theorem 4.18(ii), as formalized
in `HermiteReduction`.

## Inputs

- `HermiteReduction` (`Langlands.LinearAlgebra.Hermite`): `IsPosDef`,
  `sq_le_mul` (Cauchy–Schwarz), `det_pos`, and `exists_reduced_basis`
  (bounded Gram entries for bounded determinant).
- `RationalAdelicLattice` (`Langlands.Global.RationalLattice`):
  `IsIntegral` (all entries in `Ẑ`), `exists_int_of_isIntegral`
  (`ℚ ∩ Ẑ = ℤ` entrywise), `exists_intCast_smul_isIntegral`,
  `exists_rat_mul_integral` (`X = B W`, `GL_n(𝔸_f) = GL_n(ℚ) GL_n(Ẑ)`) and
  `exists_pos_rat_mul_unit` (`c = r u`).
- `DefiniteTraceForm` (`Langlands.Shimura.AlgebraInvolution`): the trace
  form `traceForm`, `rightMulMatrix`, `exists_leftMulMatrix_eq`,
  `points_leftMulMatrix_transpose_mul_gram`, `leftMulMatrix_one_tmul`,
  `rightMulMatrix_one_tmul`, `dotProduct_toMatrix_traceForm_mulVec_pos`,
  `exists_dotProduct_mulVec_le_traceForm` and `apply_mul_self_eq_of_gram`.
- Published: `σ.FiniteAdelicPoints`, `σ.finiteAdelicDiagonal` (`Adelic`),
  `EquivariantForms.DoubleCosets` (`EquivariantFormsDoubleCoset`), and
  `exists_intCast_eq_of_mem_integralFiniteAdeles` (`PositiveArithmeticFinite`).

## Declarations

### Integer quadratic forms

- `isSymm_toBilin'`, `isPosDef_toBilin'`: a symmetric integer matrix `S` with
  `vᵀ S v > 0` for nonzero integer `v` gives a symmetric `IsPosDef` bilinear
  form `Matrix.toBilin' S` on `ℤ^n`.
- `finite_setOf_dotProduct_mulVec_le`: for such `S` and any `T`, the set
  `{v ∈ ℤ^n | vᵀ S v ≤ T}` is finite. Put `d = det S > 0` (`det_pos`) and
  `y = adj(S) e_i`. Then `vᵀ S y = d v_i` and `yᵀ S y = d adj(S)_ii ≥ 0`, so
  Cauchy–Schwarz gives `d² v_i² ≤ (vᵀ S v) d adj(S)_ii`, and hence
  `v_i² ≤ T adj(S)_ii`. So `|v_i| ≤ |T| |adj(S)_ii|`, and `v` lies in a finite
  box.
- `exists_reduced_matrix n Δ`: there is `C` such that every such `S` with
  `det S ≤ Δ` has integer matrices `P, Q` with `P Q = 1`, `Q P = 1` and all
  entries of `Pᵀ S P` bounded by `C` in absolute value. This is
  `exists_reduced_basis` applied to `toBilin' S` on `ℤ^n`, with `P` the
  change of basis matrix to the reduced basis.

### Integral matrices and points

- `isIntegral_smul`, `isIntegral_transpose`, `map_map_intCast`,
  `map_inv_of_isUnit` (`(B⁻¹)ϕ = (Bϕ)⁻¹` for `det B` a unit),
  `isUnit_det_map`, `det_mem_of_isIntegral` (the determinant of an integral
  matrix lies in `Ẑ`): auxiliary facts on matrices over `𝔸_f`.
- `pointMatrix b g` (definition): for a point `g = (x, c)` of
  `GJ(𝔸_f) = σ.FiniteAdelicPoints`, the matrix `X` of left multiplication by
  `x` in the basis `1 ⊗ b_i` of `𝔸_f ⊗ A`.
- `pointMultiplier g` (definition): the multiplier `c` as a finite adele.
- `pointMatrix_mul`, `pointMatrix_one`, `pointMatrix_inv_mul`,
  `pointMatrix_mul_inv`, `isUnit_det_pointMatrix`, `inv_pointMatrix`,
  `pointMultiplier_mul`, `pointMultiplier_inv_mul`: both maps are
  multiplicative, and `X(g⁻¹) = X(g)⁻¹`.
- `pointMatrix_finiteAdelicDiagonal`, `pointMultiplier_finiteAdelicDiagonal`:
  for a rational similitude `ρ = (γ, t)`, the point `ρ` in `GJ(𝔸_f)` has matrix
  `L_γ` and multiplier `t`, mapped by `ϕ`.
- `pointMatrix_mul_rightMulMatrix`: `X` commutes with the image of every
  right multiplication matrix `R_y`.
- `latticeLevel σ b` (definition): the subgroup of points `g` such that
  `X(g)` and `X(g⁻¹)` are integral and `c(g), c(g⁻¹) ∈ Ẑ`
  (`mem_latticeLevel`). It is closed under products and inverses because
  integral matrices and `Ẑ` are closed under products.

### Reductions

- `IsReduction b g B r` (structure): `det B` is a unit, `r > 0`, the matrices
  `X⁻¹ Bϕ` and `(Bϕ)⁻¹ X` are integral, and `c ϕ(r)⁻¹` and `ϕ(r) c⁻¹` lie in
  `Ẑ`. So `X = Bϕ W` with `W = (Bϕ)⁻¹ X` integral with integral inverse, and
  `c = ϕ(r) u` with `u` a unit of `Ẑ`.
- `exists_isReduction`: every point has a reduction, by
  `exists_rat_mul_integral` for `X` and `exists_pos_rat_mul_unit` for `c`.
- `IsReduction.mul_right`: if `Q P = 1` for integer matrices, then `(B P, r)`
  is again a reduction.

### Equal data give equal double cosets

- `gram σ b` (definition, abbreviation): the Gram matrix `G` of the trace
  form in the basis `b`.
- `mk_eq_of_isReduction`: let `(B, r)` reduce `g` and `(B', r')` reduce `g'`.
  Suppose `r⁻¹ Bᵀ G B = r'⁻¹ B'ᵀ G B'` and `B⁻¹ R_k B = B'⁻¹ R_k B'` for all
  `k`, where `R_k` is the matrix of right multiplication by `b_k`. Then `g`
  and `g'` have the same class in `GJ(ℚ) \ GJ(𝔸_f) / K₀`. Proof:
  `Γ = B' B⁻¹` and `Γ' = B B'⁻¹` commute with every `R_k`, so they are the
  matrices of left multiplication by some `γ` and `δ`
  (`exists_leftMulMatrix_eq`), with `γ δ = δ γ = 1`. Next,
  `Γᵀ G Γ = (r' / r) G`, so `σ(γ) γ = r' / r` (`apply_mul_self_eq_of_gram`),
  and `ρ = (γ, r' / r)` is a rational similitude. Let
  `k = g⁻¹ ρ⁻¹ g'`. Its matrix is `(X⁻¹ Bϕ)((B'ϕ)⁻¹ X')`, the matrix of `k⁻¹`
  is `(X'⁻¹ B'ϕ)((Bϕ)⁻¹ X)`, and its multipliers are
  `(ϕ(r) c⁻¹)(c' ϕ(r')⁻¹)` and `(ϕ(r') c'⁻¹)(c ϕ(r)⁻¹)`. All of these are
  integral, so `k ∈ K₀` and `g' = ρ g k`.

### Bounds

- `gram_transpose`: `G` is symmetric, since the trace form is.
- `pointMatrix_transpose_mul_gram`: `Xᵀ Gϕ X = c Gϕ`.
- `map_smul_rat`, `dotProduct_transpose_mul_mul_mulVec`
  (`vᵀ (Bᵀ G B) v = (B v)ᵀ G (B v)`), `intCast_dotProduct_mulVec`,
  `intCast_map_mul`: auxiliary identities.
- `map_smul_gram`: with `V = X⁻¹ Bϕ`, the matrix `((N / r) Bᵀ G B)ϕ` equals
  `(c ϕ(r)⁻¹) Vᵀ (N Gϕ) V`. This uses `Bϕ = X V` and
  `pointMatrix_transpose_mul_gram`.
- `IsReduction.isIntegral_map_smul_gram`: if `N Gϕ` is integral, then so is
  `((N / r) Bᵀ G B)ϕ`. Hence `S = (N / r) Bᵀ G B` is an integer matrix.
- `IsReduction.exists_det_eq`: if `S = (N / r) Bᵀ G B` and `G₀ = N G` are
  integer matrices and `det S ≠ 0`, then `det G₀ = z det S` for an integer
  `z`. From `map_smul_gram`, `Wᵀ Sϕ W = u G₀ϕ` with `u = c ϕ(r)⁻¹`, so
  `ϕ(det G₀ / det S) = u'^n (det W)²` with `u' = ϕ(r) c⁻¹`. This lies in
  `Ẑ`, and a rational number in `Ẑ` is an integer.
- `IsReduction.dotProduct_pos`: for `N > 0`, `S` is positive definite:
  `vᵀ S v = (N / r) (B v)ᵀ G (B v) > 0`, since `B v ≠ 0` and `G` is positive
  definite (`dotProduct_toMatrix_traceForm_mulVec_pos`).
- `transpose_eq_of_map_eq`: `S` is symmetric.
- `IsReduction.map_conj_rightMulMatrix`: `(B⁻¹ R_y B)ϕ = W R_yϕ V`, because
  `X` commutes with `R_yϕ`.
- `IsReduction.isIntegral_map_smul_conj`: if `N' R_yϕ` is integral, then so
  is `(N' B⁻¹ R_y B)ϕ`. Hence `N' B⁻¹ R_y B` is an integer matrix.
- `conj_dotProduct_le`: if `wᵀ (Rᵀ G R) w ≤ C wᵀ G w` for all `w`, then
  `(K x)ᵀ (Bᵀ G B)(K x) ≤ C xᵀ (Bᵀ G B) x` for `K = B⁻¹ R B`, because
  `B K x = R B x`.
- `exists_int_smul`: every rational matrix has a positive integer multiple
  with integer entries.

### The main theorem

`finite_doubleCosets_latticeLevel b hpos`. The proof fixes the following
data:

- a positive integer `N` with `G₀ = N G` integral; `det G₀ ≠ 0` because `G`
  is positive definite;
- a positive integer `N'` with every `N' R_k` integral;
- constants `C_k` with `wᵀ (R_kᵀ G R_k) w ≤ C_k wᵀ G w`
  (`exists_dotProduct_mulVec_le_traceForm`), and `C = ∑ C_k`;
- the Hermite constant `C₁` of `exists_reduced_matrix n |det G₀|`, and
  `T = N'² C C₁`.

Let `𝒮` be the finite set of symmetric positive definite integer matrices
with entries bounded by `C₁`. Let `𝒟` be the set of pairs
`(S, (v_{k,j}))` with `S ∈ 𝒮` and every `v_{k,j}` in the finite set
`{v | vᵀ S v ≤ T}` (`finite_setOf_dotProduct_mulVec_le`). Then `𝒟` is finite.

For each point `g`, the proof picks a reduction `(B₀, r)` and the integer
matrix `S₀ = (N / r) B₀ᵀ G B₀`. It is symmetric, positive definite, and has
`det S₀ ≤ |det G₀|` by `exists_det_eq` with `z ≠ 0`. Hermite reduction gives
`P, Q`, and `(B, r) = (B₀ P, r)` is a reduction whose matrix
`S = (N / r) Bᵀ G B = Pᵀ S₀ P` has entries bounded by `C₁`. The columns
`v_{k,j}` of the integer matrices `M_k = N' B⁻¹ R_k B` satisfy
`v_{k,j}ᵀ S v_{k,j} ≤ N'² C_k S_jj ≤ T` by `conj_dotProduct_le`. So the data
`(S, (v_{k,j}))` of `g` lie in `𝒟`.

Choose these data for the representative `q.out` of every double coset `q`.
The resulting map to `𝒟` is injective: equal data give
`r⁻¹ Bᵀ G B = r'⁻¹ B'ᵀ G B'` and `B⁻¹ R_k B = B'⁻¹ R_k B'`, so the
representatives lie in the same double coset by `mk_eq_of_isReduction`.

## Qualifications

- Only the lattice levels `K₀ = latticeLevel σ b` are treated. Deducing
  finiteness for arbitrary compact open `K` needs compactness of `K₀` and is
  not part of this module.
- The positivity hypothesis `(σ.baseChange ℝ).IsPositive` is assumed. For
  Harris's group it follows from the published
  `isPositive_of_hasDefiniteSignature`.
- The basis is indexed by `Fin n`, as required by the published Hermite
  reduction; any `ℚ`-basis can be reindexed this way.
