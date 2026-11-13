# Weight idempotents in a finite algebra unit group

This internal generalization extracts weight idempotents from an arbitrary
split-torus morphism into the unit group of a finite free algebra. The base is
an arbitrary field K, the algebra A is an associative unital K-algebra with a
specified finite basis b, and the torus index I is finite. No centrality,
simplicity, reduced norm condition, or characteristic assumption is used.

The definitions `universalUnit` and `weightElement` take the universal torus
point in K[Z^I] tensor A and the coefficients of its inverse. The published
inverse-right-regular representation identifies each coefficient weight matrix
with right multiplication by the corresponding algebra element. The existing
weight projector identities imply that these elements are orthogonal
idempotents summing to one, vanish off the finite support, and are nonzero on
that support. The inverse universal unit is their finite monomial expansion.
If the original torus morphism is a monomorphism on underlying schemes, the
occurring weights generate the full integer lattice, by faithfulness of the
regular representation and the published universal quotient-lattice argument.

The proofs generalize the coefficient and projector arguments in
`SimplyConnected.MatrixNormOneSplitRankUpper`. The coefficient maps from that
module and their intrinsic identities are reused directly. This module does
not use that module's norm relation or split-rank bound. It constructs and
proves properties of the idempotents; extracting isotropic subspaces from an
isometry condition remains a separate step.
