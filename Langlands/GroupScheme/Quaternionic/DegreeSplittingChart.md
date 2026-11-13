# Splitting an algebra with an involution of the first kind, in any degree

Lean module: `Langlands.GroupScheme.Quaternionic.DegreeSplittingChart`
(namespace `Langlands.GroupScheme.Quaternionic.DegreeSplitting`).

This internal module is the first step of the general-degree splitting of the groups
`σ.symplecticGroup H` used in the proof of `TypeCDistinguishedVerticesStatement`. It works with
an algebra `D` over a field `K` with an involution of the first kind `σ`
(`FirstKindInvolution K D`), a field extension `L` of `K`, a finite index type `ι` with
decidable equality, and a matrix chart `e : L ⊗[K] D ≃ₐ[L] M_ι(L)`. It proves three things:
the chart extends to every commutative `L`-algebra, `σ` becomes `X ↦ S Xᵀ S⁻¹` in the chart,
and `S` is symmetric when the symmetric elements of `σ` form a space of dimension
`δ (δ + 1) / 2`, where `δ = |ι|`.

It generalises the Library module `Quaternionic.SplittingChart`, which treats `ι = Fin 2`. The
first two parts follow that module's proofs with `Fin 2` replaced by `ι`. The third part has a
new proof, because the `2 × 2` argument there does not generalise.

## Extending the chart

Let `R` be a commutative ring with compatible `K`- and `L`-algebra structures
(`IsScalarTower K L R`). The Library's `ReducedNorm.splittingMap e R : R ⊗[K] D →ₐ[R] M_ι(R)`
sends `r ⊗ d` to `r • e(1 ⊗ d)` with entries mapped into `R`.

* `splittingMap_eq_comp`: this map is the composite of three equivalences: Mathlib's
  cancellation of the base change `R ⊗[L] (L ⊗[K] D) ≃ R ⊗[K] D` (inverted), the chart
  applied after `R ⊗[L] -`, and Mathlib's matrix–tensor comparison `R ⊗[L] M_ι(L) ≃ M_ι(R)`
  (inverted). The proof checks pure tensors.
* `bijective_splittingMap`: hence the map is bijective. `chartR e R : R ⊗[K] D ≃+* M_ι(R)` is
  the resulting ring isomorphism (`chartR_apply`).
* `chartR_tmul`: `chartR e R (r ⊗ d) = r • (e (1 ⊗ d)).map (algebraMap L R)`.
* `chartR_naturality`: `chartR` commutes with every `L`-algebra map `f : R → R'`. The map
  `f ⊗ id` on the left corresponds to applying `f` entrywise on the right.

## Transporting the involution

* `transposedInvolution e σ` is the `L`-algebra automorphism `X ↦ (e (σ_L (e⁻¹ X)))ᵀ` of
  `M_ι(L)`, where `σ_L = σ.baseChange L`. The transpose turns the anti-automorphism into an
  automorphism.
* `exists_involutionMatrix` and `involutionMatrix e σ`: by Skolem–Noether in the form
  `MatrixAlgebra.exists_unit_conj_of_algEquiv`, this automorphism is conjugation
  `X ↦ U X U⁻¹` by a unit `U`. With `S = (U⁻¹)ᵀ`, `chart_baseChange` states
  `e (σ_L y) = S (e y)ᵀ S⁻¹`.
* `chartR_baseChange`: the same formula over every `R`, with `S` and `S⁻¹` mapped into `R`:
  `chartR e R (σ_R y) = S (chartR e R y)ᵀ S⁻¹`. Proof: induction on tensors, using
  `chart_baseChange` on `1 ⊗ d`.

## Symmetry of `S`

* `exists_transpose_involutionMatrix_eq_smul` (for nonempty `ι`): `Sᵀ = c S` for some `c` with
  `c c = 1`. Applying the formula twice and using `σ σ = id` shows that `W = S (S⁻¹)ᵀ`
  commutes with every matrix. Mathlib's `Matrix.center_eq_range` makes `W` a scalar `c`, so
  `S = c Sᵀ` and `Sᵀ = c S`. Then `S = c² S` with `S` invertible gives `c² = 1`.
* `finrank_antisymmetric_le`: if `2 ≠ 0` in `L`, every `L`-subspace `V` of `M_ι(L)` consisting
  of matrices with `Mᵀ = -M` has dimension at most `C(|ι|, 2)`. The proof maps `M` to its
  strictly upper triangular entries (for an ordering `ι ≃ Fin |ι|`). This map is injective,
  because antisymmetry and `2 ≠ 0` force the diagonal to vanish and determine the lower
  triangle. The index set of strictly upper triangular positions is counted against Mathlib's
  `Sym2.card_subtype_not_diag`.
* `involutionMatrix_transpose`: if `D` is finite-dimensional and
  `finrank K σ.symmetricSubspace = |ι| (|ι| + 1) / 2`, then `Sᵀ = S`. For empty `ι` this is
  trivial. Otherwise `c = ±1`. If `c = 1`, or if `2 = 0` in `L` (so `-1 = 1`), it is
  immediate. If `c = -1` and `2 ≠ 0`, every `σ_L`-symmetric `y` has `e(y) S` antisymmetric,
  since `e(y) S = S e(y)ᵀ` and `Sᵀ = -S`. The `L`-linear map `z ↦ e(ι z) S` on
  `L ⊗[K] σ.symmetricSubspace` is injective. Here `ι` is the base change of the inclusion,
  injective because `L` is flat over `K`. Its image consists of antisymmetric matrices, so
  `finrank_antisymmetric_le` bounds its dimension by `δ (δ - 1) / 2`. But the source has
  dimension `δ (δ + 1) / 2` (Mathlib's `Module.finrank_baseChange`), and
  `δ (δ + 1) / 2 ≤ δ (δ - 1) / 2` fails for `δ > 0`.

## Provenance

Over a splitting field, an involution of the first kind of a central simple algebra of degree
`δ` is `X ↦ S Xᵀ S⁻¹` with `Sᵀ = ±S`. In characteristic different from two, `S` is symmetric
(orthogonal type) exactly when the symmetric elements have dimension `δ (δ + 1) / 2`, and
antisymmetric (symplectic type) exactly when they have dimension `δ (δ - 1) / 2`
(Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*, §2). The module asserts only `Sᵀ = S`
under the dimension hypothesis (`involutionMatrix_transpose`). That holds in every
characteristic: in characteristic two, `-1 = 1` makes it immediate. The module makes no claim
about the type of `σ`.

The proofs were written for this module from the Library's Skolem–Noether theorem and Mathlib,
following the Library's `Quaternionic.SplittingChart`.
