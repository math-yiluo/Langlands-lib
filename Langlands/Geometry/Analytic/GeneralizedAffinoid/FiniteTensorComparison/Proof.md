# Finite Banach ordinary tensor comparison

This module proves `AffinoidPushout.FiniteTensorComparisonStatement`
for arbitrary presented positive-radius affinoids over a complete ultrametric
normed field. The first map is finite Banach, and the second is any bounded map.
The canonical comparison is the exact map from `C ⊗[A] B` to the actual analytic
closed-quotient pushout defined in the paired statement module. No nontrivial
valuation, strict radius, nonzero algebra or nonempty spectrum is required.
This is an internal prerequisite; unrestricted analytic étale pointwise lifting
and geometric étale base change are not proved here.

## Coefficient quotient

For a finite generating tuple `b` in `B`, `coefficientSum` sends a tuple `w` over
`C` to the sum of `tensorLeft (w k) * tensorRight (b k)`. Its tensor relation
identifies coefficients mapped from `A` with the right factor of the original
coefficient sum. Tensor induction proves surjectivity whenever the original
coefficient map is surjective. Its additive kernel is a `C`-submodule of the
finite free module `C^n`. The coefficient quotient is additively equivalent to
the ordinary tensor product: `coefficientSection` chooses coefficients, and
any two choices have the same class exactly when their coefficient sums agree.

The quotient seminorm bounds the action of `C` and of the scalar field. Choosing
coefficients for each product of two generators shows submultiplicativity up
to a common bound on these finitely many coefficient tuples. These estimates
pass from all representatives to the quotient by the existing general quotient
norm lemmas in `StrictTestDomain/FiniteRationalTensorComparisonProof`.
The two factor maps are bounded: the left factor acts on the class of one,
and the right factor uses the assumed norm-controlled coefficient lifts and
the boundedness of the original changed-base map. The canonical comparison is
bounded by summing its values on coefficient terms.

## Complete normed algebra model

`exists_structure_bound` chooses the product coefficients and bounds each by
the sum of their finitely many norms plus one. This gives a positive real
constant `D` even when the rank is zero. It requires no scalar of large norm.
`bijective_tensorComparison_of_generators` uses
`PresentedAffinoidAlgebra.isClosed_submodule_pi` to make the coefficient kernel
closed in the original product norm. Thus the quotient is a complete normed
additive group. Its ultrametric inequality is the existing quotient inequality.

The norm on the ordinary tensor product is `D` times the norm of its coefficient
class. `AddGroupNorm.toNormedAddCommGroup` constructs the corresponding normed
additive group directly. Injectivity of the coefficient section makes the norm
definite. The multiplication estimate with bound `D` becomes ordinary
submultiplicativity for this scaled norm. Scalar boundedness gives the normed
`K`-algebra structure, and positive real scaling preserves the ultrametric
inequality. The coefficient section is Lipschitz with constant `1 / D` and
antilipschitz with constant `D`, hence uniformly inducing. Its surjectivity
transfers completeness from the coefficient quotient.

The previously established factor-map and comparison bounds rescale to this
norm. The conditional bounded-pushout criterion in the statement module now
applies with the identity ring equivalence, proving bijectivity of the original
canonical comparison. `tensorComparison_bijective` obtains the finite tuple and
its norm-controlled lifts directly from `f.IsFiniteBanach`, and
`finiteTensorComparison` closes the exact Library proposition.

## Provenance

This proof generalizes the coefficient-quotient construction in the existing
finite rational tensor comparison proof. General positive radii use the new
strict scalar-extension descent theorem for closed submodules; arbitrary scalar
valuations use positive real rescaling in place of multiplication by a field
scalar. The actual bounded pushout maps and universal property are unchanged.
No new external-source assertion is used. The Lean file's dependencies and
its correspondence with the statement were checked.
