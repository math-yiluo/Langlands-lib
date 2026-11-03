# Regularity of the modular character of a nonarchimedean group

Author: Worker 103.

`Langlands.Haar.ModularCharacterRegularityStatement` is a proposition definition
awaiting proof. For every locally compact nonarchimedean group `G : Type u`,
it asserts that Mathlib's modular character has open kernel, is locally
constant, is continuous, and takes the value one on every compact subgroup.
The quantifiers include every universe. The statement assumes neither
second countability nor Hausdorffness.

The topology and group operations are the supplied instances;
`NonarchimedeanGroup G` includes continuity of the group operations and an
identity-neighborhood basis of open subgroups. Subgroups carry the subspace
topology. Compactness in the final clause means compactness of the subgroup's
underlying subset of `G`. The character is exactly
`MeasureTheory.Measure.modularCharacter`, with Mathlib's internally chosen
Borel measurable space and Haar-scaling convention. No chosen Haar measure
or measurable-space instance is an input.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Section II.3.7, printed page 47 / PDF page 53, defines the modular function
and asserts its triviality on every compact subgroup, proved by compactness
of its image in the positive reals. The page was read and its modular-function
formulas checked against the printed source.

The open-kernel, local-constancy and continuity clauses are internal
prerequisites for that argument in the nonarchimedean setting; they are not
attributed to a separately numbered assertion in Renard. Mathlib's pinned
`MeasureTheory/Group/ModularCharacter.lean` lists continuity as a TODO.
The statement makes these obligations explicit. Renard's modular convention
is the reciprocal of Mathlib's; all four properties are invariant under
taking this reciprocal.

This unit establishes no proof, no unimodularity of a general reductive
rational-point group, and no parabolic modular-character identity. Its
intended consumer is the exact actual-group target
`Langlands.Aubert.General.RationalPointFamily.RationalParabolicModulusStatement`.
