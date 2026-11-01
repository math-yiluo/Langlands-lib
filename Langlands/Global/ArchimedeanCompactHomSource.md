# Actual compact Hom sources for fixed-vector generation

This internal construction forms the conjugation action on linear maps between
two actual finite continuous compact representations. A chosen finite basis
identifies the Hom space with the canonical complex coordinate model. Joint
continuity is proved by the actual matrix identity for postcomposition and
precomposition: the transported action is multiplication by the target matrix
and by the inverse source matrix. No topology on the algebraic Hom carrier is
needed.

Postcomposition by an equivariant source map into an arbitrary complex module
gives `compactHomSourceMap`. Its image consists exactly of the linear maps whose
values lie in the original source image. The reverse implication chooses
preimages of the images of a finite basis and extends linearly, so the source
map need not be injective.

The Hom source map is equivariant for the conjugation compact actions. If the
target has a genuine complex enveloping action compatible with compact
conjugation, the pointwise action on the Hom space has the same compatibility.
If the original source image is stable under actual compact Lie generators,
the Hom source image is stable too, by its pointwise range characterization.

All constructions retain arbitrary number-field and target universes and every
natural rank. They prepare the application of fixed-vector central generation
to intertwiners. They do not yet identify the full generated Hom module or prove
the actual compact-type central-span statement or automorphic growth.
