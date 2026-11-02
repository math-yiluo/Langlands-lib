# A reflection representation and distinct simple indices

This module constructs `simpleReflectionRepresentation cs` and proves
`simple_reflection_injective cs` in
`Langlands.Group.RelativeWeylIndexing`. The parameters are independent
universes `B : Type u`, `W : Type v`, a group structure on `W`, a finite
index type `B`, a Coxeter matrix `M`, and `cs : CoxeterSystem M W`.
There is no finiteness assumption on `W`, and the empty index type is
included.

The construction and proof are internal auxiliaries to the published
Jacquet cancellation target. They are derived directly from the Coxeter
presentation and Mathlib's complex roots of unity and module reflection
APIs. This module makes no claim of correspondence with an actual relative
root system, Levi subgroup, or a representation theoretic construction,
and does not assert faithfulness of the constructed homomorphism.

For `n : ℕ`, put

```text
q(n) = exp(2π√(-1)/(2n)).
```

On `V = B → ℂ`, let `e_i` be the coordinate vector with entry `1` at `i`.
The linear form `f_i` has coordinate coefficients

```text
C(i,i) = 2,
C(i,j) = -(q(M(i,j)) + q(M(i,j))⁻¹)    if i ≠ j.
```

Thus `f_i(e_i) = 2`, and Mathlib's `Module.reflection` gives the
involutive linear equivalence `R_i(z) = z - f_i(z)e_i`.
The representation is the homomorphism obtained by applying
`CoxeterSystem.lift` to this family.

The proof of the required presentation relations treats the diagonal and
zero matrix entries separately. On the diagonal, the reflection is an
involution and `M(i,i) = 1`. A zero exponent imposes the trivial relation.
For distinct indices with `n = M(i,j) > 0`, the Coxeter matrix axioms give
`n ≥ 2`. Mathlib's `Complex.isPrimitiveRoot_exp` shows that `q(n)` is a
primitive `2n`-th root, so it is nonzero, its square is not `1`, and its
`2n`-th power is `1`. Matrix symmetry gives both off-diagonal coefficients.

The private lemma `reflection_pair_relation` proves the relation for two
abstract reflections `R_x` and `R_y` with these cross coefficients. If
`q = q(n)`, their product `T = R_x R_y` has eigenvectors
`u = q x + y` and `v = q⁻¹ x + y`, with eigenvalues `q²` and `q⁻²`.
Consequently `Tⁿ` fixes both eigenvectors. Since `q - q⁻¹ ≠ 0`, it fixes
`x` and `y`. To handle an arbitrary vector `z`, put
`c = q + q⁻¹` and `D = 4 - c² = -(q - q⁻¹)² ≠ 0`.
The vector

```text
z₀ = z - ((2 f(z) + c g(z))/D)x - ((c f(z) + 2 g(z))/D)y
```

is killed by both linear forms, and hence is fixed by both reflections.
The decomposition of `z` into `z₀`, `x`, and `y` proves `Tⁿ = 1`.
The private `pow_eigen` lemma supplies the power calculation; all scalar
identities and decompositions are proved in Lean.

Finally, equality `cs.simple i = cs.simple j` implies equality `R_i = R_j`
after applying the constructed homomorphism. If `i ≠ j`, evaluate both
maps at `e_i`, then at coordinate `i`. The two values are `-1` and `1`,
respectively, a contradiction in `ℂ`. This proves injectivity.

The actual imports are `Mathlib.GroupTheory.Coxeter.Basic`,
`Mathlib.LinearAlgebra.Reflection`, `Mathlib.LinearAlgebra.Pi`,
`Mathlib.RingTheory.RootsOfUnity.Complex`, and `Mathlib.Tactic.Module`.
No later relative Weyl target is assumed.
