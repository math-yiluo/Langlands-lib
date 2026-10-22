# Topology of the actual left-coset quotient

Worker 113 proves topological prerequisites for quotient integration on the
published `Langlands.QuotientIntegration.LeftQuotient H`, whose cosets are `H g`.
The existing quotient and its topology are unchanged. The abbreviation
`leftQuotientMap H` reuses `Langlands.Induction.quotientMap H` from
`Langlands.Representation.Induction.Definitions`: it sends `g` to the class
of `g` under `QuotientGroup.rightRel H`. This retains the analysis interface
without a second implementation of the projection. The representative formula
is definitional. The accompanying lemmas supply the topological API required
for compactly supported averaging on this actual quotient.

This is an internal derivation from pinned Mathlib. In
`Mathlib/GroupTheory/Coset/Defs.lean`, `QuotientGroup.rightRel H` is defined as
`MulAction.orbitRel H G` for the subgroup's left multiplication action. Thus
`MulAction.isOpenQuotientMap_quotientMk` applies directly to the published
quotient projection. Its `locallyCompactSpace` consequence proves local
compactness when the ambient group is locally compact.

For a closed subgroup, Mathlib's proper-action instances first show that the
ambient group's action on itself is proper, then restrict it along the closed
subgroup embedding. The theorem
`t2Space_quotient_mulAction_of_properSMul` consequently proves Hausdorffness
of the same orbit space. These facts come from
`Mathlib/Topology/Algebra/ProperAction/Basic.lean`.

No normality, countability, Haar measure or quotient-measure existence is
assumed. Ambient Hausdorffness is not needed for these topological lemmas;
they apply in particular under the locally compact Hausdorff hypotheses of
the compatible-measure existence task. They do not construct a measure.

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
