# Faithfulness of the actual descended inner action

This internal derived development proves faithfulness of the published actual
adjoint-quotient inner action. `AutomorphicAction.IsFaithful` requires that two
acting points agree whenever their actions agree on every relative test scheme.
The quantification includes arbitrary nonreduced tests and all refinements.

The implemented proof first reduces faithfulness of any automorphic action to
triviality of its all-test kernel. For `IsAdjointQuotient.innerAction`, it lifts
an acting point along the flat surjective quotient only after a base change.
The lift conjugates every point trivially, so it lies in the full
scheme-theoretic centre. The published centre-kernel comparison kills the lift;
faithfully flat descent then proves that the original quotient point is the
identity. No lift over the original test scheme is assumed, and no smoothness
of the centre is used.

`innerAction_point_ext_of_isogeny` tests the actions after any actual finite,
flat, surjective group-scheme homomorphism. It lifts target points locally along
that homomorphism, uses naturality, and applies the preceding faithfulness result.
The homomorphism may be inseparable, noncentral, and have a nonsmooth kernel.

The provenance is internal: these are formal consequences of the already
published quotient and action laws in `Adjoint.Quotient`, `Adjoint.InnerAction`
and `ActionDescent`, intended for the uniqueness part of
`SplitIsogenyUniquenessStatement`. They do not prove conjugator existence.

The faithfulness predicate, kernel criterion and `innerAction_isFaithful` are imported from `Rational.InnerDiscrepancy`. The explicit-refinement kernel interface here wraps its existing `innerAction_kernel`; the isogeny consequence uses the canonical implicit test-scheme binders.
