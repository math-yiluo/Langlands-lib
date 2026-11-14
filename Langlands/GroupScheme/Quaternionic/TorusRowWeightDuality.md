# Polar duality for full-torus row weights

This is an internal algebraic prerequisite for the maximal split torus weight
theorem. It uses the actual isometry group, the universal inverse torus point,
and the row weight spaces defined in `TorusCocharacterWeightSpace`. It is valid
over every field, including finite fields and characteristic two.

Let `K` be a field, `D` a finite-dimensional division `K`-algebra, and `σ` an
involution of the first kind. Let `q` be a quaternionic quadratic form on the
finite left `D`-module of rows `n → D`, and let `i` be any morphism from a
standard split torus indexed by a finite type `I` to the actual isometry group
of `q`. Injectivity and maximality of `i` are not needed.

The definition `torusPolarWeightBlock σ q i m p` is the matrix
`e_m * polar(q) * σ.matrix n e_p`, where `e_m` and `e_p` are the universal
inverse-action weight idempotents. Its definition uses the same signs as the
published inverse-right row action.

The algebraic proof first observes that `z + τ(z) = 0` for an alternating
element `z`. This observation is proved for a commutative coefficient ring,
so it also applies to the involution after extension to a commutative
`K`-algebra. Adding an isometry defect to its involution shows that preserving
the quadratic class implies preserving the polar Gram matrix. This argument
uses no division by two.

At the universal inverse torus point over `K[ℤ^I]`, expand this polar
invariance equation in the universal idempotents. The coefficient of exponent
`ν` on the left is the sum of `e_a * polar(q) * σ.matrix n e_b` over
`a + b = ν`; the right side has only exponent zero. Multiplication on the
left by `e_m` and on the right by `σ.matrix n e_p` isolates the `(m,p)` block
by orthogonality of the idempotents. Taking `ν = m + p ≠ 0` proves
`torusPolarWeightBlock_eq_zero`. Idempotents outside the finite support
already vanish. The coefficient argument works over arbitrary fields and
does not use density of rational torus points.

Every row in a row weight space is fixed by the corresponding idempotent.
Changing both arguments of the sesquilinear form by those idempotents gives
`sesqForm_eq_zero_of_mem_torusRowWeightSpace`: the polar form pairs the row
spaces of `m` and `p` to zero whenever `m + p ≠ 0`.

Finally, assume `q` is nondegenerate in the published polar sense. The row
spaces span the whole row module. The proved general polar duality lemma
`finrank_eq_neg_of_polar_orthogonal` therefore gives
`finrank_torusRowWeightSpace_eq_neg`: the left `D`-dimensions of the spaces
of `m` and `-m` are equal. This is the sole theorem here requiring
nondegeneracy. The module does not assert multiplicity one, rank equal to the
Witt index, or the exact maximal split torus statement.
