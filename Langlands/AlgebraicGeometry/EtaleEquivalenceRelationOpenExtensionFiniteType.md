# A finite type first level from an open extension

This derived internal helper implements the RA/PO step of the registered Stacks
Project proof of Proposition 70.8.1, Tag 07SU, using the affine open-model theorem
of Tag 07RN. The source is `stacks-noetherian-approximation-2026-11-01`. It
constructs one finite type level, with its actual cartesian comparison; it does
not assume or prove the final first-level statement.

`AffineFiniteTypeFirstLevel E` stores an étale equivalence relation, an actual
cartesian morphism from `E`, an affine object scheme locally of finite type over
the absolute terminal scheme, and affine arrows. Its object is Noetherian by the
published finite-type-over-the-integers local Noetherian theorem and compactness
of an affine scheme. `locallyOfFiniteType_terminal_spec` translates the existing
finite-presentation theorem over `Spec ULift ℤ` across the unique isomorphism of
terminal schemes. `AffineFiniteTypeFirstLevel.ofCartesian` composes the supplied
cartesian comparison with an existing first level.

`CartesianDiagram.nonempty_affineFiniteTypeFirstLevel_openExtension` assumes an
actual cofiltered cartesian diagram with affine object transitions, compact
objects locally of finite type over the integers, compact quasi-separated arrow
schemes, separated sources, and the supplied object limit. The nonidentity arrows
of the limit are assumed affine. The ambient object of the open extension is an
affine scheme containing that limit object as an open subscheme.

The proof first descends affineness of the actual nonidentity-arrow diagram to an
index `i`. The affine open-model theorem at an index `j` above `i` gives a finite
type integer algebra, its spectrum, an open immersion of the level object into
that spectrum, and the compatible pullback square. Affineness of the nonidentity
arrows persists along `j → i`. The actual open extension at `j` has affine arrows
by the coproduct decomposition into the new affine unit scheme and the affine
nonidentity arrows. The proved comparison construction gives the cartesian map
of the original open extension to this level. Every endpoint uses the same
index `j`; the proof does not descend two endpoint maps independently.
