# NYLL intermediate quotient equivalence onto its image

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Source module:
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean`.
M071.005, lines 102–117 (declaration at 104):
`ClassFormation.transferNormNaturalityIntermediateQuotientEquiv` maps to
`Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateQuotientEquiv`.
This is a same-module prerequisite included by the task's dependency clause.

## Meaning and construction

For closed subgroups `L ≤ K' ≤ K`, with `L` normal inside both `K` and `K'`,
this is the actual multiplicative equivalence between `K'/L` and its image
subgroup inside `K/L`. It applies `MulEquiv.ofBijective` to the range restriction
of the published intermediate inclusion homomorphism. The injectivity certificate
uses the independently published M071.003 theorem; surjectivity is Mathlib's
`MonoidHom.rangeRestrict_surjective`. All proof terms in the source construction
are retained.

The universe-polymorphic telescope is implicit `G : Type u`, `[Group G]`,
`[TopologicalSpace G]`, explicit `K K' L`, `hLK'`, `hK'K`, and the two named
normality instances `hLnormal` and `hL'normal`, in source order. No finiteness or
topological-group assumption is present in the source or introduced here.

## Modifications

Prefix the source namespace with `Langlands.NYLL`. Replace broad source imports
by the focused published M071.003 proof module, which also imports the actual
M071.001 inclusion and M071.004 image subgroup. The source abbreviation
`CyclicCohomology.extensionSubgroup X Y h` is expanded to its exact Mathlib body
`Y.toSubgroup.subgroupOf X.toSubgroup`, from
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`. Containment proof
parameters stay in the telescope. Preserve the `noncomputable def` and its complete
body; omit unused scope openings and all other source units. No global instance
is introduced.

## Validation and scope

Development check `50e9139c-acd3-4a58-b622-eabcf6c585dd`, in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled this definition together
with a private source-comparison module, with zero errors and warnings.
That module reconstructs the original constant with the original extension-subgroup
abbreviation and checks equality of the entire unapplied constants by `rfl`.
This checks the complete telescope and construction. It is development verification;
independent semantic review and publication remain separate requirements.
