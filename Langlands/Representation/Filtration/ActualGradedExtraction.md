# Actual smooth grades and irreducible subquotient extraction

Author: Worker 19.

This is an internal algebraic construction for the ambient extraction step
in repeated-factor Jacquet transfer. It reuses actual smooth graded
objects and proves a finite-filtration extraction lemma. It does not prove
either repeated-factor transfer or any rank-three product structure.

`ObjectRepFiltration.smoothGradedObject s j` is the actual smooth quotient
of the upper filtration step by the lower step pulled back to it. Its
representation is definitionally the published `s.gradedRepresentation j`.
It uses the existing invariant submodule and quotient constructions, with
no replacement occurrence relation. The name is an abbreviation for the
existing `SmoothRep.IrreducibleGrothendieckProof.gradedSmooth`, extracted
unchanged into [`SmoothGradedObject`](SmoothGradedObject.md).

`exists_smoothGradedObject_subquotient` takes a finite filtration `s` of an
actual smooth representation `A`, an irreducible actual smooth representation
`D`, and `SmoothRep.IsSubquotient D A`. It returns an index `j` and the actual
relation `SmoothRep.IsSubquotient D (s.smoothGradedObject j)`. The
coefficient field, group and carrier universes are independent. Both smooth
objects share the carrier universe required by the existing subquotient
relation. The group has arbitrary topology. The filtration may have repeated
steps and arbitrary graded objects, including zero objects. There are no
admissibility or finite-length assumptions apart from the supplied finite
filtration. In particular this is not the stronger assertion that `D` is
isomorphic to an entire grade.

The proof presents the given occurrence as a surjective intertwiner from
an actual subspace `S` of `A` to `D`. Starting from the zero step and ending
at the full step, it chooses consecutive steps where the restriction of
this map first becomes nonzero. Let `X` be the intersection of `S` with the
upper step. Its map to the actual grade has kernel contained in the kernel
of its map to `D`, since the latter vanishes on the lower step. Quotienting
`X` by the first kernel gives an actual smooth object injecting into the
grade and surjecting onto `D`. Irreducibility of `D` proves surjectivity of
the nonzero map. The existing presentation criterion constructs the
required actual subquotient.

This proof is derived elementary module algebra. Its first-nonzero-step
argument adapts the published `simpleSubquotientFactor` argument, but does
not assume that the grades are simple. The quotient descent is an explicit
`Submodule.liftQ` with equivariance checked on quotient representatives.
There is no reliance on a representation classification or on any printed
rank-three uniqueness assertion.

## Dependency boundary

The direct imports are `Filtration.SmoothGradedObject`,
`Classification.SupercuspidalSupport` and `Filtration.SubsingletonProof`.
The first supplies the shared actual grade. From `SupercuspidalSupport`
the proof uses only the
explicit injective/surjective presentation criterion for actual smooth
subquotients and elementary isomorphism surjectivity. These are proved
there by ranges, kernels and the first isomorphism theorem; no support
existence or uniqueness is invoked. From `SubsingletonProof` it uses only the
criterion that a vector has zero image in the actual grade exactly when
it lies in the lower step. The remaining steps are quotient lifting,
finite induction and the simple-module fact that a nonzero map onto an
irreducible object is surjective.

A pre-integration recursive audit of all 65 project modules in the original import closure found
only the lower definitions and elementary algebraic, smoothness, twist,
and normalization proofs. The classification-named imports are
`ConstituentRelations`, `Segments`, `Supercuspidal`,
`SupercuspidalSupport` and `SupercuspidalTwist`; they do not import any of
the eight excluded classification tasks' conclusions. The implemented
proof uses no global support decomposition, ordered quotient coverage,
multisegment classification, segment-head irreducibility, or local
rank-three assertion. A declaration inspection reports only
`propext`, `Classical.choice` and `Quot.sound`, with independent universe
parameters `uK`, `uG`, `uV`. This inspection is a development check;
independent review and publication remain required.
