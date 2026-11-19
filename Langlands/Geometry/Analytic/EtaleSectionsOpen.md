# Sections of analytic étale maps are open immersions

The section result is the graph case of the local diagonal property in Berkovich, *Étale cohomology for non-Archimedean analytic spaces*, Proposition 3.3.7(c) and the proof of Corollary 3.3.9. The Lean argument proves the result directly from equality over unramified pieces.

An ordinary point in the image of a section lifts to a field-valued point by taking the completed residue field of a containing base chart and applying the section. The retraction followed by the section fixes this full field point and has the same composite to the base as the identity.

Represent the two maps by strong maps on a common quasi-isomorphism refinement. Because the étale representative is unramified over every finite affinoid piece, the maps agree on an open analytic neighbourhood of the lifted point. Transport that open domain along the quasi-isomorphism. Local identity on the image of the section gives the analytic identification of the section with its open image. Arrow isomorphisms transport the result to every localized étale map.

The same local equality proves that the diagonal into any actual self-pullback of an étale map is an open immersion. A field-valued point on the diagonal has the same image under both projections. Their local equality and pullback uniqueness show that the first projection followed by the diagonal is locally the identity. The argument uses the universal property of the given pullback and the étale property of its original map.
