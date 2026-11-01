# Strict filtered comparison for the actual Cartan tensor action

This is an internal extension of the actual scalar restriction comparison to
bounded Cartan tensors and compact fixed covariants. The coefficient and tensor
degree bounds are the existing actual monomial spans. The constructions retain
arbitrary field and module universes and every natural rank; the central
specializations additionally use the existing number field hypothesis.

For a complex linear source map `j` into a genuine compatible enveloping module,
`cartanTensorActionRestrictionError` is the complex linear difference between
acting on the tensor action image by the whole symmetrization of `P`, and first
multiplying the tensor by the actual Cartan restriction of `P`. Its displayed
application formula exposes those two actual actions.

Assume the range of `j` is stable under every actual compact Lie generator. For
coefficient degree at most `p` and tensor degree at most `q`, the error lies in
`F_(p+q-1) • range j`. Induction on the bounded tensor span reduces this to a pure
tensor. There it is exactly the existing scalar action comparison, with `j(v)`
in the stable range. Linearity of the error map handles sums and complex scalars.
This is a strict degree reduction when `p+q` is positive.

The total degree-zero case is treated separately: induction on the actual whole
symmetric degree-zero span shows that every such coefficient is an algebra
scalar. Its whole symmetrization and its Cartan restriction are the same scalar
in their respective algebras, and compatible scalar towers make the action
comparison exact. This equality in fact holds for every tensor degree whenever
the coefficient has degree zero, with no source-stability assumption.

For an actual full-group invariant coefficient, its symmetrization is the
existing actual central symmetrization, and its action on a fixed covariant is
multiplication by its actual Cartan restriction after inclusion. Substitution
gives `centralSymmetrize_cartanCovariant_action_sub_mem`, with the same bound and
stability hypothesis, and exact equality at coefficient degree zero.

The results use only the previous scalar comparison, actual tensor action and
actual full-group invariant scalar action. They provide the filtered comparison
needed for central generation; they do not themselves prove central generation,
admissibility or the automorphic differential growth theorem.
