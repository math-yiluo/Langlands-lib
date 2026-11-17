# Čech systems from compact lifted tuple cones

This internal construction connects the unproved
`CompactCompatibleTupleConesStatement ρ` to the actual finite free Čech
system used in the compact quasi-étale comparison. It proves a conditional
implication and does not prove that geometric existence statement.

`CompactCompatibleTupleConesStatement.cechPresentation` chooses the actual
cones and their limit witnesses supplied by its hypothesis. Each cone point,
its compact Hausdorff property and its continuous action lift give an index of
`CompactLiftBasis ρ`. Its basis object is the cone point itself, so the
basis-point isomorphism is the identity. Applying
`FiniteBasisCover.cechPresentationOfCones` gives a finite representable
coproduct presentation in every degree of the actual cover's presheaf Čech
nerve. This construction requires local smallness at the chosen universe `w`.

`finiteCechSystem` supplies these presentations to
`compactCompatibleCechSystem`. It retains that construction's hypotheses:
a topological group, finite equivariant refinements, local smallness at the
coefficient universe, module-valued sheafification and the locally bijective
description of its local equivalences. It constructs the actual augmented
free Čech system with the proved exactness and local lifting fields of
`compactCompatibleCechSystem`.

The provenance is internal: choose the witnesses of the geometric statement
and apply the existing categorical presentation and Čech-system
constructions. The analytic space has universes `LocalizedCategory.{u,v,v}`;
the group and coefficient universes remain independent. Coefficient `Hom`
acyclicity, geometric existence, and the final global comparison theorem
remain separate proof obligations.
