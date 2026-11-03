# Reduction of actual augmentation support to graded ideal generation

This module derives the actual group-scheme semigroup comparison from three
explicit prerequisites: general positive generation for a graded proper ideal,
the actual coordinate weight decomposition with same-character quotient
lifting, and the actual cotangent/Lie support comparison. Its definitions are
those of the published `CoordinateAction`, `CoordinateCotangent` and
`CoordinateSemigroupStatement` modules.

The explicit definition `augmentationGradedMul` supplies Mathlib's homogeneous-multiplication structure
on the actual ideal eigenspaces, directly from `mul_mem_weightSpace`. It
requires neither a unit in the ideal nor a chosen internal decomposition.
This structure is passed explicitly to supply the multiplication premise in the
generic ideal theorem.

`augmentationIdeal_ne_top` evaluates one at the identity to show that the
augmentation ideal is proper. Under local finite type,
`isNoetherianRing_coord` applies the published `Lie.coordinateAlgebraFiniteType`
and the Noetherian property of a field.
Smoothness and connectedness are needed later for the published domain
theorem `CharacterLatticeProof.isDomain_coord`.

`cotangentLiftSupport_eq` uses the explicitly assumed image equality at each
character to identify the generic homogeneous-lift support with the existing
actual cotangent support. A lift gives a quotient eigenvector; conversely,
image membership supplies a homogeneous lift of each nonzero eigenvector.
The actual cotangent quotient map is unchanged.

`support_eq_closure_cotangent_of_gradedIdeal` applies the generic proper-ideal
positive-generation statement to the actual augmentation ideal. Its internal
decomposition and same-character lifting are explicit premises, and products
have the sum of the labels by `mul_mem_weightSpace`. The published domain and
finite-type results discharge the geometric commutative algebra hypotheses.
The raw support on the two interfaces is definitionally the same.

`coordinateSemigroupComparison_of_prerequisites` extracts the internal ideal
decomposition and quotient lifting from the actual decomposition statement,
then rewrites cotangent support using the explicit Lie-support comparison.
The previous support-algebra reduction supplies the containment criterion for
every additive subsemigroup. Positive closure preserves the empty-support case
without inserting zero.

These are derived conditional reductions of the argument in
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), §3.3,
Example 3.3.2, printed pp.107–108 / PDF pp.133–134. This module does not prove
any of the three prerequisite statements.
