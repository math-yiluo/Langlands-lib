# Derived-torus intersections from existing structural inputs

Author: Worker 1435.

This internal reduction proves
`derivedMaximalTorusIntersection_of_structuralInputs` with type
`DerivedMaximalTorusIntersectionReductionStatement.{u}`. Its two assumptions
are the existing `MaximalTorusCentralizerStatement.{u}` and
`DerivedMaximalSplitTorusStatement.{u}`. Its conclusion is the exact
`DerivedMaximalTorusIntersectionStatement.{u}`. Neither assumption is proved
here, and this conditional result is not an unconditional proof of the
intersection or cocenter statements.

First, `IsDerivedSubgroup.isConnectedReductive` proves connected reductivity
of the source of an actual derived inclusion in a connected reductive group.
It applies the published derived smoothness and connectedness theorems and
then the theorem that a smooth connected normal closed subgroup of a
connected reductive group is connected reductive. Normality and closedness
come from the actual derived-subgroup predicate. This step assumes no separate
semisimplicity theorem or extra hypotheses about the derived source.

Over an algebraically closed field, every torus is split by the finite Galois
splitting theorem. The assumed derived maximal split torus statement supplies
a maximal split torus of the derived group contained in the specified ambient
maximal torus. It is a maximal torus because every torus over that field is
split. The derived source is connected reductive by the first step, so the
assumed self-centralizer statement identifies the entire centralizer of this
source torus with its own range.

The generic full-pullback comparison
`isTorus_subgroupIntersection_of_selfCentralizing_of_reflection`, with the
first map equal to the identity on the derived source, identifies the entire
pullback `D ×_G T` with that source torus. Its commutation argument is valid on
all test schemes: the two images commute in the commutative ambient torus,
and the closed derived inclusion reflects their commutation. Symmetry of the
pullback gives the claimed torus structure on `T ×_G D`. This retains every
part of the intersection scheme.

For an arbitrary ground field, extend to its algebraic closure. Connected
reductivity and the actual derived inclusion base change by their published
theorems. The assumed self-centralizer statement makes the original maximal
torus geometrically maximal through the existing self-centralizer
base-change comparison. Apply the algebraically closed argument.
`subgroupIntersectionBaseChangeIso` then identifies the resulting intersection
with the base change of the original one, and `IsTorus.of_baseChange`
descends the torus property.

All fields, arbitrary universe `u`, and the original full intersection are
retained. The construction combines named Library results and the two explicit
structural inputs; it does not use the cocenter statement or replace its
remaining structural proofs by hypotheses of the final target.
