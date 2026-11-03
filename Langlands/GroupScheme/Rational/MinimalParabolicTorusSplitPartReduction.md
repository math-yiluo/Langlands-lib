# The minimal-parabolic split-part theorem from rational Levi geometry

Authors: Worker 1348 and Worker 1361.

This module proves a conditional reduction to two universe-general geometric
statements. It imports the unchanged
`MinimalParabolicTorusSplitPartStatement` and introduces no alternative version
of that target. The conditional reduction does not establish either premise,
and is not an unconditional proof or completion of the target.

The premise `ParabolicRadicalTorusLeviStatement` supplies, for an actual maximal
torus `t : T → G` factoring through the given parabolic `j : P → G`, a
geometric solvable radical `r : R → P`, a torus `S` mapping into `T` and `R`,
and a rational Levi `l : L → P`. Its `sL : S → L` is a largest central
subtorus and satisfies `sL ≫ l = sT ≫ f`. The premise also records the
radical-intersection equality, maximality in the radical and the centralizer
description of that Levi; the reduction needs only its existence,
largest-central-subtorus property and commuting diagram.

The second premise, `MinimalParabolicLeviCentralizerStatement`, applies to
this same Levi and radical when `P` is minimal. It supplies
`bR : B → R` whose ambient composite `bR ≫ r ≫ j` is maximal split and
whose all-test whole-torus centralizer equals `range (l ≫ j)`.
The closed morphism `l ≫ j` therefore represents that centralizer.
The diagram for `sL` and `f ≫ j = t` give
`sT ≫ t = sL ≫ (l ≫ j)`.

The proof then applies
`IsMaximalSplitTorus.ambient_transfer_of_centralizer_center`.
The supplied ambient maximal split torus becomes closed and central in its
represented centralizer; the greatest-central-torus property of `sL` factors
it through `S`, hence through `T`. The ambient transfer gives maximal
splitness of `a ≫ t` and centralizer containment in `range j` for every
maximal split subtorus `a` of `T`. Containment
`range (l ≫ j) ≤ range j` is witnessed by the actual factor `l` on every
test scheme. Smoothness and affineness of `G`, supplied by connected
reductivity, provide the local finite-type and affine hypotheses of that
transfer. No restriction on the ground field is introduced.

`MinimalParabolicTorusSplitPartReductionStatement` is precisely the implication
from the two named geometric statements to the original target.
`minimalParabolicTorusSplitPartReduction` proves this Prop-valued statement
using
`minimalParabolicTorusSplitPartStatement_of_radical_torus_levi`.
The final theorem of the proof task still requires actual published proofs
of both geometric premises; neither is inferred from the publication of its
statement.

The provenance is internal. Worker 1348 authored this Lean assembly and
documentation. Worker 1361 authored the geometric statement interfaces used
as explicit premises and contributed the source decomposition motivating them.
All new proof steps are actual-morphism composition, represented-subgroup
factorization and the previously proved conditional central-torus transfer.
