# The full simply connected normalizer image over the maximal unramified extension

Authors: Worker 185 and Worker 4348.

`Langlands.Geometry.Building.MaximalUnramified.simplyConnectedNormalizerAffineWeyl`
proves the unchanged published proposition
`Langlands.Geometry.Building.MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u}`
at arbitrary universe `u`, with no additional premises.

For every original nonarchimedean local field `F`, every affine simply connected
group `G` over `K = Langlands.LocalGalois.Separable.inertiaFixedField F`, and
every supplied `C : MaximalUnramified.BuildingData F G`, the conclusion is

```text
C.apartment.normalizerAffineEquiv.range =
  AffineRootSystem.affineWeylGroup C.affineRoots.
```

The proof applies
`simplyConnectedNormalizerAffineWeyl_of_quasiSplitRootGeneration` to the
unconditional theorem
`Langlands.GroupScheme.quasiSplitSimplyConnectedRootGeneration`.
The latter proves rational root generation over every field for quasi-split
simply connected groups and every supplied maximal split torus.
Its implementation constructs equivariant simple-coroot coordinates and proves
generation orbit by orbit, using the orthogonal and A₂ cases, then descends
centralizer points and applies the centralizer-covering theorem.

The imported maximal-unramified reduction proves that the particular group `G`
is quasi-split using the actual normalized valuation of `K`, its Henselian
valuation subring, and its algebraically closed residue field. Rational root
generation then supplies the premise of the integer-valued reflection and
normalizer generation theorem on the same supplied datum `C`. This gives the
equality of the full original normalizer image with the reflection-generated
affine Weyl group of `C.affineRoots`.

All quantifiers of the published proposition are retained, including rank zero
and groups that do not descend to `F`. The proof requires no additional AS 5,
Tits-system, facet-fixing or apartment-comparison premise. Its provenance is
internal composition of the two imported results; the source comparison for
the target remains in its unchanged statement Markdown. This module proves
the supplied-data image equality and constructs no new building.
