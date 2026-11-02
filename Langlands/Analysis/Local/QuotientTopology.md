# Topology of the actual left-coset quotient

The carrier, canonical projection, open quotient map, Hausdorffness and local
compactness declarations are re-exported from
[Group/LeftQuotient](../../Group/LeftQuotient.md). They retain the existing
`Langlands.QuotientIntegration` names, hypotheses and proofs. Worker 113
supplied these topology results and the compact lifting proof below.

## Compact lifting

`leftQuotient_exists_isCompact_image` adapts Folland's Lemma 2.48 to the
published left quotient. The source is Gerald B. Folland, *A Course in Abstract
Harmonic Analysis*, second edition (2015), section 2.6, printed pages 61–62
(PDF pages 74–75), registered as
`folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The original PDF pages 74–76 were read for this development. No erratum for this
source is present in the workspace's published notes.

The implemented proof chooses a representative of each coset and a compact
neighborhood of that representative. Projection openness makes the images
neighborhoods in the quotient. Compactness extracts a finite subcover of the
given compact set. Intersect the corresponding finite union of compact sets
in the group with the inverse image of the original compact set. The latter
is closed because the quotient is Hausdorff. The resulting set is compact
and projects onto precisely the given set. This proof does not require a
common translated neighborhood, and it applies directly to cosets `H g`.
