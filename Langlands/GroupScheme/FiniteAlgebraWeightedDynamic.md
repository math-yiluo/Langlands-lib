# Weighted diagonal cocharacters of finite matrix-algebra unit groups

Module `Langlands.GroupScheme.FiniteAlgebraWeightedDynamic`, namespace
`Langlands.GroupScheme.FiniteAlgebraUnits.WeightedRoot`.

Setting: `k` a field, `D` a `k`-algebra (only `Ring D` is assumed), `n` a finite index type,
`b` a `k`-basis of `M_n(D)`, and `groupScheme b` the published unit group scheme of `M_n(D)`.
On a test scheme `T` with coefficient ring `R = Γ(T)`,
`MatrixPoints.tensorMatrixEquiv k D b T` identifies points with `GL_n(R ⊗ D)`. Scalars from
`R` enter as central elements `r ⊗ 1`. All characteristics are allowed.

## Matrix algebra

For a commutative ring `R`, an `R`-algebra `S` and a weight function `w : n → ℤ`:

- `weightMatrix w t` / `weightMatrixHom w : Rˣ →* GL_n(S)`: the diagonal unit
  `diag(t^{w i})` (entries `algebraMap R S (t^{w i})`).
- `weightMatrix_conj_apply`: `(diag(t^w) M diag(t^w)⁻¹) i j = t^{w i - w j} M i j`.
- `weightMatrix_add`, `weightMatrix_neg`: the diagonal is additive in the weights.
- `swapMatrix a b`, `swapUnit a b`: the permutation matrix of the transposition of `a` and
  `b`, a unit equal to its own inverse. `swapUnit_conj_weightMatrix`: conjugation by it
  permutes the weights. `map_swapUnit`: any ring map preserves it.
- `indicatorWeight a` (`1` at `a`, `0` elsewhere) and `pairWeight a b` (`1` at `a`, `-1` at
  `b`, `0` elsewhere). `pairWeight_mem`: for `a ≠ b` all values lie in `{-1, 0, 1}`.
  `weightMatrix_pairWeight`: `diag(t^{pairWeight a b}) = μ (π μ π⁻¹)⁻¹` with
  `μ = diag(t^{indicatorWeight a})` and `π = swapUnit a b`.
- `map_weightMatrix`: compatibility with coefficient ring maps.
- `IsWeightStrict w M`: `M i j = 0` whenever `w i ≤ w j`. `cube_eq_zero`: if all weights lie
  in `{-1, 0, 1}`, such `M` satisfies `M³ = 0` (a nonzero product would need a strictly
  decreasing chain of four weights).
- `unipotentUnit M hM`: `1 + M` with inverse `1 - M + M²`, for `M³ = 0`.
- `scale w s M`: the matrix `s^{(w i - w j)₊} M i j`, with `isWeightStrict_scale`,
  `isWeightStrict_map`, `map_scale`, `scale_zero` (at `s = 0` a weight-strict matrix
  vanishes).
- `isWeightStrict_sub_one`, `map_contracting`: `u - 1` is weight-strict when `u` has
  contracting shape (`u i j = δ i j` whenever `w i ≤ w j`), and ring maps preserve this shape.
- `weightMatrix_conj_eq`: for `U` of contracting shape,
  `diag(t^w) U diag(t^w)⁻¹ = 1 + scale w t (U - 1)`.

## The cocharacter

- `cocharacterPoints k D b w T`: the homomorphism from `T`-points of `𝔾_m` to `T`-points of
  the unit group, `t ↦ diag(t^{w i})`. `cocharacterPoints_naturality` proves naturality;
  `cocharacter k D b w := homOfPoints ...` is the resulting group-scheme homomorphism over the
  ground field, and `tensorMatrixEquiv_cocharacter` gives its matrix on every test.

## Contraction

Fix weights with values in `{-1, 0, 1}` (`hw`), a test `T` and `u ∈ GL_n(R ⊗ D)` of contracting
shape (`hu`).

- `lineScalar T`: the coordinate of `𝔸¹`, as a central scalar on `T × 𝔸¹`.
- `curveMatrix w u = scale w s ((u - 1) pulled back to T × 𝔸¹)`, weight-strict.
- `contraction hw u hu : T × 𝔸¹ ⟶ (groupScheme b).X`: the point `1 + curveMatrix w u`.
- `tensorMatrixEquiv_comp_contraction`: its matrix after any pullback.
- `contraction_isOrbitExtension`: restricted to `T × 𝔾_m` it equals the conjugation orbit of
  `u` under the cocharacter, by `weightMatrix_conj_eq`.
- `contraction_evalZero`: at `s = 0` it is the identity.
- **`mem_unipotent_of_contracting`**: the point `(tensorMatrixEquiv T).symm u` lies in
  `Dynamic.unipotent (cocharacter k D b w)` on `T`.

## Provenance

Internal. This generalizes the published binary construction
`FiniteAlgebraBinaryDynamic` (scalar diagonal cocharacter, polynomial contraction curve,
`homOfPoints`) from `2 × 2` elementary matrices to arbitrary weighted diagonals and arbitrary
matrices of contracting shape. It reuses `BinaryRoot.tensorAlgebra`, `tensorMap` and
`includeSections` by name. The underlying mathematics is the dynamic description of unipotent
radicals of parabolic subgroups (Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, §2.1). No
statement about parabolic subgroups is made here.
