# Scalar extension of all-test cocharacter row weights

Let `K` be any field, `D` a finite-dimensional division `K`-algebra, `σ` an
involution of the first kind, `n` a finite index type, `q` a `σ`-quadratic form,
and `f : Gm → O(q)` an actual cocharacter. For every commutative coefficient
`K`-algebra `R` and integer `c`, this module constructs the canonical `R`-linear
equivalence

`R ⊗[K] cocharacterWeightSpace q f c ≃ₗ[R] cocharacterWeightSpaceOver q f R c`.

The new space is a submodule of `R ⊗[K] (n → D)`. The finite product tensor
equivalence identifies this ambient module with rows over `R ⊗[K] D`. The
definition of the space uses the actual inverse-right row operator, extended
to the relative Laurent test algebra `R ⊗[K] LaurentPolynomial K`.

More explicitly, `cocharacterExtendedCoefficientMap` inserts `R` as the first
factor, `cocharacterExtendedLaurentMap` inserts the Laurent algebra as the second
factor, and `cocharacterExtendedTestPoint` is the image of the original universal
multiplicative-group point along the latter map. `cocharacterExtendedRow` inserts
a row in this test algebra. `cocharacterExtendedMonomialRow` multiplies this row
by `1 ⊗ T^c`. The new space is the kernel of the difference between the actual
row action at that point and this monomial row.

The theorem `mem_cocharacterWeightSpaceOver_iff` proves that this single equation
is equivalent to the following all-test condition: for every commutative
`K`-algebra `S`, every `K`-algebra map `φ : R → S`, and every `S`-valued point `t`
of `Gm`, the specialization of the row along `φ` is an eigenvector of the actual
row action of `f(t)` with eigenvalue `t^c`. Here `t^c` means the integer power
of the unit corresponding to `t`. Thus the new space describes actual weights
over all coefficient extensions of `R`, including negative weights.

The implemented comparison has four steps:

1. `cocharacterWeightEquation` subtracts the required monomial row from the
   original universal row action. Its kernel is exactly the restriction to `K`
   of the published `D`-submodule `cocharacterWeightSpace q f c`, by the companion
   universal-point criterion.
2. `cocharacterExtendedEvaluation` evaluates both factors of the relative
   Laurent algebra at any coefficient map and unit. Naturality of the actual
   row action proves the all-test characterization, in both directions.
3. `cocharacterExtendedEquationEquiv` distributes tensors over the finite row
   product and rebrackets them. `cocharacterWeightEquationOver_eq` uses
   coefficient naturality and linearity to identify the actual extended
   equation with the tensor extension of the original equation through this
   equivalence.
4. Flatness over `K` and Mathlib's `LinearMap.tensorKerEquiv` identify the
   kernels. This gives `cocharacterWeightBaseChangeEquiv`. Its pure-tensor
   formula says that `r ⊗ v` maps to the same ambient tensor `r ⊗ v`.

For every field extension `L/K`, `finrank_cocharacterWeightSpaceOver` proves that
the dimension of the new space over `L` is the dimension of the original space
over `K`. The theorem `finrank_cocharacterWeightSpaceOver_eq_mul` applies the
tower law to express this as

`finrank K D * finrank D (cocharacterWeightSpace q f c)`.

In particular, if `finrank K D = degree^2`, this is `degree^2` times the original
weight dimension over `D`. No centrality of `D`, nondegeneracy of `q`, infinitude
of `K`, or characteristic restriction is assumed; empty row indices are
included. The coefficient-algebra equivalence itself permits arbitrary
commutative `R`, including algebras with nilpotents.

This is derived internal content. It combines the unchanged all-test weight
space, the companion universal-point and coefficient-action definitions,
elementary tensor identities, and preservation of kernels by tensoring over a
field. It introduces no new literature assertion. It does not construct an
orthogonal Morita equivalence or identify spin-cover weights with a numbered
type-`D` root datum.
