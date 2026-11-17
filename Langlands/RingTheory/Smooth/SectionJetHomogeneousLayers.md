# Homogeneous polynomial descriptions of actual augmentation layers

Let `R` and `A` be commutative rings, with an `R`-algebra structure on `A` and
an augmentation `ε : A →ₐ[R] R`. Put `I = ker ε`. The variables of the polynomial
ring are indexed by an arbitrary type `σ`; the universes of `R`, `A` and `σ`
are independent.

This is an internal construction from the Library's
`Algebra.SectionJet.Coordinates.jetEquiv`, the actual truncation kernel
`Algebra.SectionJet.Layer`, and Mathlib's homogeneous polynomial decomposition.
It has no additional external source claim.

`homogeneousToLayer z hz n` is the `R`-linear map from homogeneous polynomials
of degree `n+1` to the actual kernel
`ker (A/I^(n+2) → A/I^(n+1))`. It sends a polynomial `p` to the residue class
of `p(z)`. Here `z : σ → A` is any family with `ε(z s) = 0`. Membership in the
kernel follows because evaluating an element of the `(n+1)`st power of the
variable ideal lands in `I^(n+1)`. This definition does not require smoothness
or a basis.

Assume now that `A` is formally smooth over `R`, that
`b : Module.Basis σ R I.Cotangent` is a specified basis, and that `z s` lifts
`b s` under `AugmentedAlgebra.classMap ε`. Then
`homogeneousEquivLayer z b hz hzb n` is an `R`-linear equivalence. There is no
finite-type, finite-rank, field, noetherian or constant-rank hypothesis.

The implemented injectivity proof uses the injectivity of evaluation on
polynomials modulo the `(n+2)`nd power of the variable ideal. A homogeneous
polynomial of degree `n+1` in that ideal power has all its coefficients zero.
For surjectivity, represent an element of the layer by a polynomial using the
order-`n+1` coordinate equivalence. Its vanishing under lower truncation
implies that the polynomial lies in the `(n+1)`st variable-ideal power.
Removing its homogeneous component of degree `n+1` raises that ideal order
to `n+2`, so this component has the same image in the layer.

The auxiliary results `homogeneous_mem_idealOfVars_pow`,
`homogeneous_eq_zero_of_mem_pow`, and `sub_homogeneousComponent_mem_pow`
are proved directly by coefficient support and degree. The equivalence uses the
specified lifts; independence of lifts, changes of basis, sheaf comparisons and
determinant formulas are outside this module.
