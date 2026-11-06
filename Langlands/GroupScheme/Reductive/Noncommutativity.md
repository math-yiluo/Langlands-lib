# Noncommuting points of nontrivial semisimple field groups

For an arbitrary field `k` and semisimple group scheme `G`, the construction
`IsSemisimple.noncommutingPoints` chooses a test scheme `U` over `Spec k`
and two morphisms `U ⟶ G.X` that do not commute. Its hypothesis says that
the image of the identity homomorphism is not the trivial subgroup functor.
It does not assert the existence of noncommuting `k`-rational points.

The helper `IsSemisimple.noncommutative_of_nontrivial` supplies the
corresponding universally quantified noncommutativity assertion. Neither
declaration assumes that the field is algebraically closed.

This is an internal construction from existing Library definitions and
proofs. If every pair of points commuted, the identity homomorphism would
factor through the actual finite scheme-theoretic centre. This makes the
whole group scheme finite. The Library theorem `finiteHom_cancel`, applied
to the homomorphism from `G` to the actual trivial group scheme, identifies
the identity endomorphism with the constant unit endomorphism. Its hypotheses
hold because a semisimple group is smooth, connected and affine. Every
point is then the unit, contradicting the stated nontriviality.
Classical choice applied to this contradiction gives the chosen test and
noncommuting pair.

The existing helper in `Reductive.MinimalNormalFactor` has an algebraically
closed field hypothesis. This separate module makes the arbitrary-field
consequence available without altering that module or its callers. It is
a helper for rational-generation induction; it supplies no normal-complement
existence theorem or factor decomposition.
