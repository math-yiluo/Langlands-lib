# Closed scalar-extension quotient embeddings through the Galois Weil unit

Let `L/F` be a finite Galois extension of number fields in arbitrary common
universe `u`, with its specified algebra structure, and let `G` be an affine
group scheme locally of finite type over `F`. This module constructs
`AdelicGaloisUnit.scalarExtensionQuotientMap F L G` and proves that it is a
closed topological embedding

```text
NormOneRationalQuotient F G
  → NormOneRationalQuotient L (AffineWeil.unitBaseChange F L G).
```

The target group is the actual pullback base change. The map is the composite
of the original quotient map induced by `AffineWeil.unit F L G` and the
canonical adelic Weil quotient map. `scalarExtensionQuotientMap_mk` records
its exact action on representatives: apply the unit on actual norm-one
points, then the fixed canonical adelic Weil comparison.

`hasCompactNormOneRationalCover_of_baseChange` consequently proves that
compact principal representatives for the actual upper-field base change
give compact principal representatives for `G` over `F`.
No reductivity, connectedness, commutativity or normality assumption is made.
All norm-one subgroups, principal maps, and quotient topologies are the
existing ones, retaining the normalized absolute values of all rational
algebraic characters.

The proof is internal and proceeds through the actual ground-field group
`W = AffineWeil.groupScheme F L (AffineWeil.unitBaseChange F L G)`.

1. `unitMap` is the existing continuous adelic map of the actual algebraic
   unit. Its proved closed immersion makes it a topological embedding.
   `unitRangeEquiv` therefore identifies the original source adelic group
   homeomorphically and multiplicatively with the unit image.

2. `mem_unitRange_iff` specializes the all-affine-test Galois fixed-image
   theorem to the original full adele algebra of `F`. The conjugation maps
   are actual `F`-group-scheme endomorphisms of `W`, so their adelic maps
   are continuous and preserve the principal rational subgroup.

3. `map_rationalSubgroup_unitRange` identifies the source principal subgroup
   with the intersection of the ambient principal subgroup and the unit
   image. In the nontrivial direction, an ambient principal point in the
   image is fixed on adeles. Injectivity of the original principal map
   makes its rational point fixed as well. Applying the same all-affine-test
   fixed-image theorem over `F` descends it to an actual rational point of `G`.

4. The published actual adelic topology on `W` is Hausdorff and sequential,
   and its rational subgroup is closed and discrete. The finite family
   of Galois conjugation endomorphisms therefore satisfies
   `LeftCosetSpace.isClosedEmbedding_subgroupInclusion_fixed`.
   Transport through `unitRangeEquiv` and the exact rational subgroup
   identification proves that `fullQuotientMap` is a closed embedding on
   the full actual rational quotients.

5. The square with the existing norm-one quotient inclusions commutes on
   representatives. The source inclusion is closed, so the composite into
   the full target quotient is a closed embedding. Factoring it through the
   target inclusion proves the closed embedding of the original
   `normOneRationalQuotientMap` of the unit.

6. Compose with the proved forward Weil norm-one quotient embedding to
   obtain the displayed scalar-extension closed embedding. If the target
   has compact principal representatives, its quotient is compact. The
   closed embedding makes the source quotient compact; the published
   local compactness argument then constructs compact representatives
   in the original source norm-one group.

The argument needs neither classification of all Weil-restriction characters
nor the general arbitrary closed-algebraic-subgroup quotient theorem.
It does not prove compactness of the upper-field group or the parent
central-split compactness theorem.
