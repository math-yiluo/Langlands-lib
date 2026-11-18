# Representability of the scheme of maximal tori

Worker 586.

`Langlands.GroupScheme.maximalTorusScheme` proves the published
`MaximalTorusSchemeStatement.{u}` for every universe `u`, with no additional
hypotheses. For every scheme `S` and reductive group scheme `G` over `S`,
it supplies a smooth, surjective parameter scheme `M` and a universal closed
relative torus in `G_M` that is maximal on every residue-field fibre.
Universality holds for every `S`-scheme and uses equality of the actual
subgroup functors. Above each affine open of `S`, the parameter scheme is
quasi-affine.

This is a derived assembly of published Library results. The source and
scope of the target, Conrad's *Reductive group schemes* (2014),
Theorem 3.2.6, first assertion for reductive groups, are recorded in the
[statement's Markdown](MaximalTorusSchemeStatement.md). The proof uses the
following three inputs.

- [`MaximalModuliOpen`](MaximalModuliOpen.md),
  `TorusSubgroupModuli.exists_smooth_isUniversalMaximal`, constructs the
  smooth universal maximal family as the open maximality locus in the
  universal family of closed relative tori.
- [`EtaleLocalMaximalExistenceProof`](EtaleLocalMaximalExistenceProof.md),
  `etaleLocalMaximalTorusExistence`, supplies an etale cover with a closed
  fibrewise maximal relative torus on each member.
- [`MaximalTorusModuliQuasiAffineProof`](MaximalTorusModuliQuasiAffineProof.md),
  `maximalTorusModuliQuasiAffine`, proves quasi-affineness above every
  affine base open for any supplied universal maximal family.

The new helper `TorusSubgroupModuli.IsUniversalMaximal.surjective_of_cover`
proves surjectivity of the parameter map. Given a point `s` of `S`, choose
a point `x` on a cover member lying over `s`. The maximal torus on that
member has a classifying map into `M` by the universal property.
Evaluating this map at `x` gives a point of `M` over `s`: the equality
follows by evaluating the classifying map's equation as a morphism over
`S`. This argument uses only the supplied cover and universality.

The intermediate theorem `maximalTorusScheme_of` constructs the smooth
universal maximal family, applies the published local-existence theorem
and this helper to obtain surjectivity, and obtains the affine-open
quasi-affineness clause from its sole premise
`MaximalTorusModuliQuasiAffineStatement`. The final theorem discharges that
premise with the published unconditional
`maximalTorusModuliQuasiAffine`. All witnesses and properties concern the
same parameter scheme and universal family, and the original target
statement is unchanged.
