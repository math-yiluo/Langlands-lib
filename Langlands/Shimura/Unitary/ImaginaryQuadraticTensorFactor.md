# Scalar-extension factors and imaginary quadratic eigensubmodules

This internal algebraic comparison extends `ImaginaryQuadraticModule`. The
imaginary quadratic CM number field `L`, containing characteristic-zero field
`K`, arbitrary commutative coefficient `K`-algebra `R`, and module `M` have
the same compatible rational scalar structures as that module. The input is
an actual unital ring homomorphism `rho : L → End_R(M)`.

`tensorModule` makes `M` an actual module over `T = R ⊗[ℚ] L` by composing
the constructed `tensorAction` with the evaluation action of `End_R(M)`.
`factorAlgebra` makes `R` an actual `T`-algebra through the natural coordinate
for `false`, or the conjugate coordinate for `true`. These structures determine
the scalar-extension tensor product `R ⊗[T] M` used throughout the comparison.
Each declaration installs these structures explicitly in its type and body.
Thus the chosen action and coordinate remain part of the actual tensor product
used by its interface; no global instance chooses either of them.

The simultaneous eigensubmodule also carries a `T`-action through that
coordinate and its existing `R`-action. The tensor action commutes with
structural coefficient scalars, and both scalar evaluation and the induced
action on the eigensubmodule satisfy the scalar tower laws.

`tensorProjector` sends a vector to its constructed projector image in the
eigensubmodule. It is `T`-linear because the tensor algebra is commutative,
and its action on a projected vector is the selected scalar evaluation.
`tensorFactorToEigen` extends this map by the scalar-extension universal
property. It is an actual `R`-linear map, sending `r ⊗ m` to `r` times the
corresponding projector applied to `m`.

Tensor balancing and evaluation of the selected idempotent at one show
`r ⊗ P(m) = r ⊗ m`. Tensor induction then proves that `m ↦ 1 ⊗ m` is a left
inverse of `tensorFactorToEigen`. Every eigenvector is fixed by its projector,
so its tensor with one supplies a preimage and proves surjectivity.
`tensorFactorEquiv` packages these proofs as an actual `R`-linear equivalence
between the selected scalar-extension factor and the full simultaneous
eigensubmodule. Its pure-tensor formula and its inverse formula are proved.

All constructions and proofs are derived from the tensor universal property,
the actual splitting idempotents, and the already constructed module action.
No output comparison is an input. No finiteness, flatness, reducedness or
nontriviality assumption on the coefficient ring or module is used. This
module does not assert a sheaf comparison, a Lie-sheaf splitting, geometric
ranks, base-change compatibility or representability.
