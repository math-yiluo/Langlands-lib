# Unitary compact-overgroup maximality

`Langlands.Group.unitaryMatrixCompactOvergroup` proves the unchanged Library
proposition `Langlands.Group.UnitaryMatrixCompactOvergroupStatement`. Its complete
type is

```lean
∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ),
  Langlands.Group.UnitaryMatrixCompactOvergroupStatement 𝕜 n
```

Thus every compact subgroup `U` of `Matrix.GeneralLinearGroup (Fin n) 𝕜`
containing `Unitary.toUnits q` for every unitary matrix `q` consists of unitary
matrices. The scalar universe is arbitrary, and every natural rank, including
zero, is covered. Specializing to `ℝ` or `ℂ` gives the orthogonal or unitary
case. The concluding Lean example checks the complete unapplied theorem
constant against this telescope.

## Matrix action and unitary transitivity

The proof uses `Matrix.toEuclideanLin` to act on
`EuclideanSpace 𝕜 (Fin n)`, with its usual Euclidean norm. All matrix and units
topologies are the existing Mathlib instances from the target statement;
the proof introduces no topology instances.

The private lemma `matrix_mem_unitary_of_norm` turns a norm-preserving matrix
action into a linear isometry. Finite-dimensionality makes it a linear isometry
equivalence by `LinearIsometry.toLinearIsometryEquiv`. Its matrix in the
standard orthonormal basis is unitary by
`LinearIsometryEquiv.toMatrix_mem_unitaryGroup`. The inverse identities for
`Matrix.toEuclideanLin` and matrix representation identify that matrix with the
original one.

The private lemma `exists_unitary_map` takes nonzero `x` and equal-norm vectors
`x, y`. On the line spanned by `x`, it defines the linear map
`c • x ↦ c • y` using `LinearEquiv.coord`. Equality of the norms makes this
map a linear isometry. `LinearIsometry.extend` extends it to the whole
finite-dimensional Euclidean space. Taking its matrix and applying the preceding
lemma gives a unitary matrix sending `x` to `y`.

The private lemma `continuous_matrix_action_norm` proves continuity of
`g ↦ ‖g x‖` for each fixed vector `x`. It composes continuity of the value map
on matrix units, continuity of matrix-vector multiplication, the continuous
conversion to the Euclidean `WithLp` model, and continuity of the norm.

## Compactness and the norm bound

The private lemma `compact_overgroup_norm_le` proves `‖g x‖ ≤ ‖x‖` whenever
`g ∈ U`. If `x = 0`, linearity gives the claim immediately. Otherwise,
compactness of `U` and continuity of the action norm supply `a ∈ U` maximizing
`‖a x‖`. Write `y = a x`. Since the identity lies in `U`, maximality gives
`0 < ‖x‖ ≤ ‖y‖`.

Set `c` equal to the scalar-field image of the positive real number
`‖y‖ / ‖x‖`. Then `‖c‖ = ‖y‖ / ‖x‖`, and `y` and `c • x` have equal norm.
The transitivity lemma provides a unitary matrix `q` with
`q y = c • x`. Containment and subgroup closure put `a q a` in `U`.
Its value on `x` is `c • y`, so maximality yields

```text
(‖y‖ / ‖x‖) * ‖y‖ ≤ ‖y‖.
```

Since `‖y‖ > 0`, this implies `‖y‖ / ‖x‖ ≤ 1`, hence `‖y‖ ≤ ‖x‖`.
Every `g ∈ U` satisfies `‖g x‖ ≤ ‖y‖` by maximality, giving the desired bound.
The maximization is done separately for each nonzero vector; it does not
require selecting a unit vector or assuming positive rank.

## Closing argument and scope

Apply the norm bound to `g` at `x` and to `g⁻¹` at `g x`. Matrix
multiplication and the inverse identity give `g⁻¹ (g x) = x`, so the two bounds
give `‖g x‖ = ‖x‖`. The first helper then proves that the value matrix of `g`
belongs to Mathlib's actual unitary group.

For rank zero the Euclidean space has only the zero vector, already handled by
the zero-vector branch. No invariant form, extra maximality assumption,
determinant restriction, or positive-rank hypothesis is supplied. The module
proves the local compact-overgroup assertion only; assembling it over the
archimedean coordinates is a separate global proof.

This is an internal structural proof of the published local target.
Worker 16 proposed the compact orbit-norm maximization route in the task
contract. Worker 101 implemented the per-vector variant and the Lean proof.
It is not attributed to Borel–Jacquet or to another external literature source.
