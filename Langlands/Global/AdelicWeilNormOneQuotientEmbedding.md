# Closed embedding of actual norm-one Weil rational quotients

Let `F` and `L` be number fields in arbitrary common universe `u`, with a
specified `Algebra F L`, and let `G` be any affine group scheme locally of
finite type over `L`. The definition
`AdelicWeilRestriction.normOneQuotientMap F L G` sends

```text
NormOneRationalQuotient F (AffineWeil.groupScheme F L G)
    → NormOneRationalQuotient L G
```

by applying the fixed canonical adelic Weil map to representatives.
`isClosedEmbedding_normOneQuotientMap` proves that this exact map is a closed
topological embedding. These are the original left quotients by the actual
principal rational subgroups, with their existing quotient topologies and the
norm-one subgroups defined using all normalized rational-character norms.

The construction uses only the already proved forward norm-one inclusion.
It does not assume equality of the norm-one subgroups or classification of
characters of the Weil restriction.

The internal proof has four parts.

1. `map_rationalSubgroup` uses the published principal compatibility of the
   actual adelic Weil equivalence and the bijective rational-point comparison
   to identify the full principal subgroups in both directions.
   `rationalQuotientHomeomorph` therefore descends the full canonical
   multiplicative homeomorphism through the existing
   `LeftCosetSpace.congrHomeomorph`.

2. `normOneQuotientMap` descends the continuous homomorphism `normOneMap`.
   Its preservation of actual principal points makes the quotient map
   well-defined. `normOneQuotientMap_mk` records its exact representative
   formula.

3. `normOneQuotientInclusion_comp_normOneQuotientMap` identifies the composite
   into the upper-field full rational quotient with the source norm-one
   quotient inclusion followed by `rationalQuotientHomeomorph`.
   The source inclusion is a published closed embedding, and the latter map
   is a homeomorphism. Their composite is a closed embedding. Since the
   target norm-one quotient inclusion is an embedding, factoring through
   that inclusion proves the desired closed embedding.

4. `hasCompactNormOneRationalCover_of_upper` starts with compact principal
   representatives over `L`. The target norm-one rational quotient is then
   compact. The closed embedding makes the source quotient compact, and the
   published locally compact quotient argument constructs compact principal
   representatives for the actual ground-field Weil restriction.

All assertions retain arbitrary affine groups locally of finite type, with
no commutativity, connectedness, reductivity or splitting hypothesis, and no
Galois hypothesis on the field extension. The compact-cover implication is
conditional on compact representatives for the upper-field group. The module
does not prove general group compactness or the full
`NormOneComparisonStatement`.
