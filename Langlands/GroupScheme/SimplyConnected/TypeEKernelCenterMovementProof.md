# Full-centre movement for branch-marked E6 and E7

`rankOneTypeEKernelCenterMovement` proves the published
`RankOneTypeEKernelCenterMovementStatement` in every universe over
arbitrary fields.

The actual kernel of a branch-marked E6 group has a degree-six division
norm-one model. Its full star action is trivial by the vertex comparison
with the ambient index, so the actual obstruction is defined on every
integral kernel character.

The two ground exterior representations of the ambient group have
maximal multiplicity-one weights given by the positive-root sum and that
sum minus the marked simple root. The ground isotypic transfer supplies
two ground representations of the chosen kernel with those restricted
weights. Their Brauer obstructions vanish by ground rationality. By
additivity, the obstruction of the restricted marked root vanishes.
Ground exterior representations of the kernel also give root-span
vanishing there.

Rational inner alignment with the standard special-linear pinning
identifies the first fundamental weight of the actual column
representation and numbers all the kernel vertices. The integral kernel
relation then shows that three times this weight has zero obstruction.
The column representation's Galois intertwining equations pass along
the base change of the actual group isomorphism. They identify its Tits
algebra with the chart's fixed matrix algebra, which is the original
division algebra. Three times that Brauer class cannot vanish, since a
division algebra of degree six has nonsplit tensor cube.

The E6 branch therefore has contradictory hypotheses. For E7,
`TitsIndexData.hasCenterMovingAutomorphism_of_E7_branch_mark` supplies
an automorphism of the particular kernel of the supplied index. It acts
by inversion on the full geometric centre. A geometric central point
distinct from its inverse then contradicts full-centre fixation, which
would persist under base change. The fixation condition quantifies over
all test schemes, including nonreduced ones.

The proof uses the highest-weight transport from `SpecialLinearNumberedWeightTransport` and the degree-six class obstruction from `DivisionBrauerClass`.
