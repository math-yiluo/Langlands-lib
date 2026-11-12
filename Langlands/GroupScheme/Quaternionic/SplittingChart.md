# Splitting a quaternion algebra with an involution of the first kind

This internal module is a step toward showing that the quaternionic symplectic groups
`σ.symplecticGroup H` (in `Quaternionic.GroupSchemes`) are connected reductive. It works with
an algebra `D` over a field `K` with an involution of the first kind `σ`
(`FirstKindInvolution K D`), a field extension `L` of `K`, and a matrix chart
`e : L ⊗[K] D ≃ₐ[L] M₂(L)`. It proves three things: the chart extends to every commutative
`L`-algebra, `σ` becomes `X ↦ S Xᵀ S⁻¹` in the chart, and `S` is symmetric when the symmetric
elements of `σ` form a `3`-dimensional space.

## Extending the chart

Let `R` be a commutative ring with compatible `K`- and `L`-algebra structures
(`IsScalarTower K L R`). The Library's `ReducedNorm.splittingMap e R : R ⊗[K] D →ₐ[R] M₂(R)`
sends `r ⊗ d` to `r • e(1 ⊗ d)` with entries mapped into `R`.

* `splittingMap_eq_comp`: this map is the composite of three equivalences: Mathlib's
  cancellation of the base change `R ⊗[L] (L ⊗[K] D) ≃ R ⊗[K] D` (inverted), the chart
  applied after `R ⊗[L] -`, and Mathlib's matrix–tensor comparison
  `R ⊗[L] M₂(L) ≃ M₂(R)` (inverted). The proof checks pure tensors.
* `bijective_splittingMap`: hence the map is bijective. `chartR e R : R ⊗[K] D ≃+* M₂(R)` is
  the resulting ring isomorphism.
* `chartR_tmul`: `chartR e R (r ⊗ d) = r • (e (1 ⊗ d)).map (algebraMap L R)`.
* `chartR_naturality`: `chartR` commutes with every `L`-algebra map `f : R → R'`. The map
  `f ⊗ id` on the left corresponds to applying `f` entrywise on the right.

## Transporting the involution

* `transposedInvolution e σ` is the `L`-algebra automorphism `X ↦ (e (σ_L (e⁻¹ X)))ᵀ` of
  `M₂(L)`, where `σ_L = σ.baseChange L`. The transpose turns the anti-automorphism into an
  automorphism.
* `exists_involutionMatrix` and `involutionMatrix e σ`: by the Library's Skolem–Noether
  theorem `MatrixAlgebra.exists_unit_conj_of_algEquiv`, this automorphism is conjugation
  `X ↦ U X U⁻¹` by a unit `U`. With `S = (U⁻¹)ᵀ`, `chart_baseChange` states
  `e (σ_L y) = S (e y)ᵀ S⁻¹`.
* `chartR_baseChange`: the same formula over every `R`, with `S` and `S⁻¹` mapped into `R`:
  `chartR e R (σ_R y) = S (chartR e R y)ᵀ S⁻¹`. Proof: induction on tensors, using
  `chart_baseChange` on `1 ⊗ d`.

## Symmetry of `S`

* `exists_transpose_involutionMatrix_eq_smul`: `Sᵀ = c S` for some `c` with `c² = 1`. Applying
  the formula twice and using `σ σ = id` shows that `W = S (S⁻¹)ᵀ` commutes with every
  matrix. Mathlib's `Matrix.center_eq_range` makes `W` a scalar `c`, so `S = c Sᵀ` and
  `Sᵀ = c S`. Then `S = c² S` with `S` invertible gives `c² = 1`.
* `eq_smul_of_transpose_eq_neg`: if `2 ≠ 0`, every `2 × 2` matrix `M` with `Mᵀ = -M` equals
  `M₀₁ • !![0, 1; -1, 0]`.
* `involutionMatrix_transpose`: if `K`-dimension of the symmetric elements
  `σ.symmetricSubspace` is `3`, then `Sᵀ = S`. If `c = 1`, or if `2 = 0` in `L` (so `-1 = 1`),
  this is immediate. Otherwise `c = -1` and `2 ≠ 0`. Every symmetric `y` of `σ_L` then has
  `e(y) S` antisymmetric: `e(y) S = S e(y)ᵀ` and `Sᵀ = -S`. The `L`-linear map
  `z ↦ e(ι z) S` on `L ⊗[K] σ.symmetricSubspace` is injective. Here `ι` is the base change of
  the inclusion, injective because `L` is flat over `K`. Its image consists of `σ_L`-symmetric
  elements, so it lies in the line spanned by `!![0, 1; -1, 0]`. But
  `L ⊗[K] σ.symmetricSubspace` has `L`-dimension `3` (Mathlib's `Module.finrank_baseChange`),
  and `3 ≤ 1` is a contradiction.

## Provenance

Over a splitting field, an involution of the first kind of a quaternion algebra is
`X ↦ S Xᵀ S⁻¹` with `Sᵀ = ±S`. In characteristic different from two, `S` is symmetric
(orthogonal type) exactly when the symmetric elements have dimension `3`, and antisymmetric
(symplectic type) exactly when they have dimension `1`. In characteristic two, `-1 = 1`, so `S`
is always symmetric. There the symmetric elements have dimension `3` for both types, so the
dimension does not determine the type. For example, over `𝔽₂` the involution
`X ↦ J Xᵀ J` with `J = [[0, 1], [1, 0]]` is symplectic and fixes the `3`-dimensional space of
matrices `[[a, b], [c, a]]`. The module asserts only `Sᵀ = S` under the dimension-`3`
hypothesis (`involutionMatrix_transpose`). That holds in every characteristic, and the module
makes no claim about the type of `σ`.

The proof was written for this module from the Library's Skolem–Noether theorem and Mathlib.
In characteristic different from two, it uses only the fact that dimension `3` excludes the
antisymmetric case.
