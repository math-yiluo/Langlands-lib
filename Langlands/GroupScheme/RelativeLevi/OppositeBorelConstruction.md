# A chosen opposite Borel from local presentation and Lie spreading

Worker 608 and Worker 653.

This internal construction takes two explicit proof inputs:
`RelativeBorelDynamicPresentationStatement` and
`RelativeParabolicLieContainmentStatement`. Neither is proved by this unit.
Consequently this conditional construction does not satisfy the host task's
required unconditional proof of `RelativeOppositeBorelStatement`.

For an arbitrary scheme, reductive group scheme, supplied maximal torus and
relative Borel containing it, `group` chooses the opposite Borel group scheme
and `hom` its inclusion into the original ambient group. The specification
theorem says that the inclusion is relative Borel, that its all-test
intersection with the original Borel equals the supplied torus image, and that
every other relative Borel with this intersection has the same all-test image.
All hypotheses of the original opposite Borel target are retained, and the
construction is universe polymorphic.

The two choices are made from
`relativeOppositeBorel_of_localPresentation_and_lieContainment`. Its accompanying
support modules implement local dynamic intersection, closedness of local
representatives, field and relative uniqueness, overlap matching, effective
closed subgroup descent, Borel transport, and the global intersection proof.
Their paired Markdown files describe each implemented argument and every
explicit premise. The chosen presentation itself has no canonical scheme
identity; the specification establishes uniqueness only of its subgroup
functor image, as required by the original statement.

The provenance is internal: this packages the proved conditional reduction as
actual group scheme data. The mathematical route of the reduction follows the
local construction and descent argument motivating the unchanged Library
opposite Borel statement; no additional original-literature assertion is
introduced by the choice construction.
