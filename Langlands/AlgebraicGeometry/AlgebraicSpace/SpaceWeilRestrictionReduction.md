# Affine atlas construction for restriction of scalars

Author: Worker 110.

Derived infrastructure and a conditional assembly for Conrad's Lemma 5.10,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp.17–18. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The construction follows the source's use of an actual affine atlas.
The full lemma remains conditional on the two explicitly named geometric
input statements; this file does not prove those inputs.

`HasAtlasProperty.exists_affine_atlas` refines a quasi-compact structural
étale atlas to an actual affine one. Its structural scheme-morphism
property `P` must be stable under composition and implied by étaleness.
The scheme base is assumed compact. Starting from a scheme atlas `W`,
quasi-compactness of its structure map gives compactness of `W`.
The proof uses Mathlib's
finite affine cover domination, composes its étale surjective map with
the original atlas, and retains `P` by composition.

`affineCoordinate_finitePresentation` identifies finite presentation
of the actual coordinate algebra of an affine scheme from local finite
presentation of its structure map. The spectrum of its coordinate
algebra is canonically isomorphic to that scheme, so the scheme
property transfers along this isomorphism. The ring-hom property
then gives the algebra property.

`affineWeilRestriction_locallyOfFinitePresentation` compares the existing
finite-type Weil algebra with the published finite-presentation Weil
algebra using `finitePresentationAlgEquiv`. Finite presentation
transfers along the inverse algebra isomorphism. Its relative spectrum
is the existing affine Weil scheme, so it is locally finitely presented.
The rings remain arbitrary, with a finite projective algebra extension.

`restrictedAffineAtlas` takes a chart of `X'` from an affine scheme
`U'` locally of finite type over `Spec R'`. It composes the full
presheaf comparison from the actual affine Weil scheme with restriction
of the original chart transformation. The helper
`restrictedAffineAtlas_properties` transports étaleness and geometric
surjectivity along the isomorphism in that composite. Its geometric
hypotheses are explicitly supplied.

`spaceWeilRestriction_of_geometricInputs` has the exact implication
from `WeilRestrictionDiagonalStatement` and
`WeilRestrictionAffineEtaleAtlasStatement` to the unchanged published
`SpaceWeilRestrictionStatement`. It refines the supplied finite-type
atlas to an affine locally finite-type one, restricts it, and uses
the diagonal input and atlas input to construct the algebraic-space
witness. The same atlas proves finite type; the diagonal input gives
quasi-separatedness and separatedness. For finite presentation it
refines the separately supplied finite-presentation atlas and uses
the proved affine finite-presentation result. This need not be the
same affine atlas as the one used for the algebraic-space witness.

The two geometric input statements are assumptions of this conditional
assembly, not hidden hypotheses added to the full lemma. Their
unconditional proofs and independent publication are still needed
before this construction can yield a proof of the full lemma.
