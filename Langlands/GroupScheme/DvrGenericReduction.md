# Closing a smooth reduced generic subgroup

Worker 572.

`Langlands.GroupScheme.DvrGenericReduction.group G` is an actual flat
group scheme over a Dedekind domain `R`, constructed as the schematic
closure of the reduced generic subgroup of `G`. The construction uses
an arbitrary specified fraction field `K`. It assumes that `G` is flat
and locally of finite type over `R`, and that the canonical reduction
of its actual generic fibre is geometrically reduced over `K`.
Neither `K` nor the residue fields are assumed perfect.

The morphism `DvrGenericReduction.map G` is an actual group-scheme
homomorphism to `G`. Its underlying scheme map is a finite surjective
closed immersion. The new group is locally of finite type; it is
quasi-compact and separated whenever `G` has those properties.
Its actual generic fibre over `K` is smooth, and is affine whenever
the actual generic fibre of `G` is affine. These properties are
implemented, with the geometric-reducedness hypothesis explicit.
The construction does not supply a field or DVR extension making
that hypothesis hold, or a smooth total group.

## Implemented argument

First, `GeometricReductionSubgroup.group` constructs the actual smooth
reduced subgroup of the generic fibre. Its inclusion is a surjective
closed immersion. `GenericSubgroupClosure.closureGroup` then constructs
the flat schematic closure in the original group, including all group
operations and the closed group homomorphism. The existing generic
isomorphism `GenericSubgroupClosure.genericToClosureIso` identifies its
actual generic fibre with the reduced generic subgroup. This proves
generic smoothness and affineness by composing the structural maps
with the inverse of that isomorphism. Finite type, quasi-compactness
and separatedness follow by composing the closed inclusion with the
original structural map.

The additional theorem
`GenericSubgroupClosure.surjective_closureInclusion` proves
surjectivity for any surjective closed generic subgroup of a flat
group over a Dedekind domain. The generic-fibre projection of the
ambient flat group is schematically dominant, hence has dense range.
The surjective generic subgroup inclusion followed by this projection
therefore has dense range too. That composite factors through the
closure inclusion, so the closure inclusion has dense range. Its
range is closed because it is a closed immersion; it follows that it
is surjective. Closed immersions are finite, giving the required
finite-surjective actual homomorphism.

## Provenance

This is a reusable derived construction for the preliminary step of
Conrad's Corollary A.4, author-preprint p.29 of Prasad and Yu,
*On quasi-reductive group schemes*. The literature uses the reduced
total group. The implemented proof instead closes the reduced generic
subgroup, using the Library's schematic-closure construction. Both
routes give the stated finite surjective homomorphism and smooth
generic fibre, without invoking the later normalization argument.
The source's general Dedekind-domain scope is retained; the intended
consumer specializes it to a DVR after obtaining potential geometric
reducedness of the reduced generic fibre.

Registered source:
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
