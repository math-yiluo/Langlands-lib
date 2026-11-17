# Local Artinian detection with arbitrary target schemes

Worker 876.

This is an internal extension of the published
`Deformation.ArtinianSchemeDetection.hom_ext`. It proves noetherian
Artinian-test detection with no affine or separatedness condition on the target.
It is intended for the equality of the two multiplication morphisms that expresses
centrality in SGA 3, Exposé IX, Théorème 5.6(b).

`ArtinianDetection.hom_ext_general` states that two morphisms from a locally
noetherian scheme agree if their composites with every map from the spectrum of
a local Artinian ring in the same universe agree. First the residue-field probes
show that the underlying point maps agree. Around each source point, choose an
affine open containing its common image, and restrict the source to the
intersection of the two inverse images. The published affine-target detection
theorem applies on this locally noetherian open. Equality on these source
neighbourhoods gives equality globally.

`ArtinianDetection.over_hom_ext` is the corresponding statement in the slice
category of schemes over a fixed scheme. It follows by forgetting to schemes
and using extensionality of slice morphisms.

The noetherian hypothesis is retained. The module makes no claim of Artinian
detection for arbitrary non-noetherian source schemes. The proof is derived from
the published Artinian detection theorem and Mathlib's open-cover and
residue-field constructions; it introduces no additional mathematical premise.
