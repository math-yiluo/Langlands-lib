# Finite coefficient families of finite-rank diagonal matrices

This module constructs the finitely supported diagonal of a matrix that is a
finite sum of outer products over a commutative noetherian ring. The index type
is arbitrary and has an independent universe from the ring.

The source is SGA 3, Exposé IX, Lemma 7.2, recomposed p.58 (original margin
pp.71–72), in the registered Gille–Polo 2009 edition
`sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
It is the finite-support input to the diagonalizable case of Theorem 7.1.

For a commutative ring `A` and an arbitrary type `M`, `coefficients` is the
canonical linear map

```text
(M → A) ⊗[A] (M → A) →ₗ[A] (M × M → A),
b ⊗ c ↦ ((m,n) ↦ b(m)c(n)).
```

Thus a matrix in its image is exactly a finite sum of outer products.
`finite_support_diagonal` assumes the coefficients off the diagonal vanish
and proves that the diagonal function has finite support when `A` is
noetherian. `diagonalFinsupp` constructs the resulting element of `M →₀ A`;
`diagonalFinsupp_apply` identifies its coefficients.

The proof follows the source's module argument. Tensor induction first bounds
all columns by a single finite span in `M → A`. The inverse image of this span
under the injective inclusion `(M →₀ A) →ₗ[A] (M → A)` is finitely generated:
its image is a submodule of a finitely generated module over a noetherian
ring. The union of the supports of finitely many generators then bounds the
support of every element. Each diagonal column is the one-coordinate vector
with value the corresponding diagonal coefficient, so the bound contains every
nonzero diagonal coefficient.

The intermediate lemmas `exists_finite_column_span`, `exists_support_bound`
and `finite_support_of_single_mem_finite_span` make these steps explicit.
Only the last of these and the diagonal construction use noetherianity.
No reducedness, domain, finite index set, adic completeness, finite generation
of the index group or invertibility assumption is imposed.

This is a construction and auxiliary proof for the lifting of homomorphisms from
isotrivial groups of multiplicative type over adically complete noetherian rings. It does not prove
algebraization of formal group homomorphisms or the adic lifting statement.
