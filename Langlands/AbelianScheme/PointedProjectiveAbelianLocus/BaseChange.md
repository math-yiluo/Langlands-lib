# Base change and locality for the pointed abelian-scheme condition

`pointed_iff_overIso` obtains the pointed condition from an isomorphism over
the test scheme with an abelian scheme of relative dimension `g`. Right
translation by the inverse of the image of the prescribed section makes
the isomorphism carry that section to the unit. For base change and
iteration, `OpenCoverStructure.restrictIso` compares the iterated pullback
with the pullback along the composite.

`pointed_of_openCover` uses `abelianSchemeStructureOfOpenCover` to reconstruct
an abelian scheme. The constant relative dimension is checked on the same
open cover using Zariski locality of `SmoothOfRelativeDimension g` at the
target. The auxiliary transport lemma applies a base-change-stable morphism
property to an isomorphism over the base by viewing it as a pullback square
over the identity of the base.
