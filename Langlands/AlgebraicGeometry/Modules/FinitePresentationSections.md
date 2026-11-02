# Affine finite presentation from actual sheaf presentations

This internal derived unit connects Mathlib's actual finite presentations of
module sheaves to finite presentation of their modules of affine sections.
It imposes no noetherian condition on the scheme or its affine section rings.

`finitePresentation_sections_of_presentation` takes a finite global sheaf
presentation of a module sheaf and proves that its section module on any affine
open is finitely presented over that open's function ring. A presentation
already supplies quasi-coherence. Its generators give a surjective map on
affine sections from a finite free module, using the published
`freeSectionsIso` comparison. Its relations show that the sheaf kernel has
finitely generated affine sections. Exactness of sections at the kernel
identifies the linear kernel with the image of those kernel sections.
Mathlib's finite-presentation criterion for a quotient of a finitely presented
module by a finitely generated kernel finishes the proof.

`exists_finitePresentation_restrict` transports the finite presentation on a
covering over-site to the actual open subscheme containing a given point,
using the published `presentationRestrictOfOver` construction.
`exists_locally_finitePresentation_sections` combines these two facts: every
point has an open neighbourhood whose restricted sheaf has finitely presented
sections on every affine open in that neighbourhood.

`finitePresentationSectionNeighbourhood` chooses such an actual open
neighbourhood together with its membership and finite-presentation proofs.
The construction is noncomputable and asserts no compatibility between its
choices for different points or sheaves.

The provenance is a direct internal consequence of Mathlib's presentation
definitions and the published affine exactness and presentation-transport
APIs. This unit introduces no additional assertion from the literature.
It does not yet compare finite presentation at stalks or spread a stalk
trivialization to an open neighbourhood.
