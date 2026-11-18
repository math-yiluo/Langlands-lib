# Comparing local special fibres and closed geometric fibres

Worker 508.

This internal comparison applies to every commutative local ring `A`.
It imposes no Henselian, Noetherian, completeness or characteristic condition.

`closedPointResidueFieldIso` identifies the ring-theoretic residue field
`IsLocalRing.ResidueField A` with the scheme-theoretic residue field at the
closed point of `Spec A`. It composes the canonical quotient-to-prime-residue-field
isomorphism with the inverse of Mathlib's spectrum residue-field comparison.
`closedPointResidueFieldIso_comp_special` proves that the induced spectrum map
commutes with the actual maps to `Spec A`: the ring-theoretic special-fibre map
and the scheme's canonical residue-field point.

`closedGeometricPointFactor` factors the Library's chosen geometric point at
that closed point through `Spec (IsLocalRing.ResidueField A)`. Its composition
with `Spec.algebraMap A (IsLocalRing.ResidueField A)` is exactly the geometric
point. `specialGeometricFiberIso` combines this equality with actual pullback
composition to identify the chosen closed geometric fibre of any group
scheme over `A` with the indicated base change of its special fibre.

`isIso_geometric_of_special` applies the same base-change comparison to a
group-scheme homomorphism. If its actual special-fibre homomorphism is an
isomorphism, so is its actual closed geometric-fibre homomorphism.
There are no smoothness, flatness, affineness or commutativity hypotheses
on the group schemes.

The construction is derived from the published ring and scheme residue-field
comparisons, the Library's geometric-point definition and actual group-scheme
base-change composition. It supplies the closed-fibre comparison needed to
use a prescribed special-fibre diagonalization in the multiplicative-type
fibral criterion; it asserts no existence of a lift.
