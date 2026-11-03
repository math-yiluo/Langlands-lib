# Actual character images of associated finite root subsets

This derived unit constructs `associatedRootSetEquiv`, an equivalence between
the actual character subsets selected by a finite subset of the associated
simple labels and its image under `associatedFinsetEquiv`. Its forward map
is the published character-lattice action of `longestRep cs J`.

The field, affine ambient group, monomorphic torus inclusion, finite simple
label type and finite actual point Weyl quotient are explicit. The data
`hN` and `hZ` compare the scheme normalizer and full centralizer with the
corresponding subgroups of the actual torus point image. The two additional
premises are `RootLengthComparison` and
`PositiveSimpleReflectionComparison` for the supplied actual Coxeter
system. The unit assumes no full scheme Coxeter realization, reductivity,
maximality, genericity, characteristic restriction or local-field structure.
It does not construct either point comparison or either root-sign premise.

The construction follows three elementary steps. First,
`positiveSimpleSet_longestRep` identifies the associated labels with the
right ascents of the longest representative. `RootLengthComparison`
therefore makes their actual character images positive.
`associatedSimpleEquiv_conj` supplies the simple-reflection conjugacy.
Applying `PositiveSimpleReflectionComparison` with that positivity proves
`weylCharacterAction_associatedSimpleEquiv`, which identifies the exact
character, including its sign.

Second, the imported `rootSet_associatedFinsetEquiv` from
`RationalAssociatedLeviRestriction` provides the equality

```text
w '' rootSet (I.map subtype_K)
  = rootSet ((associatedFinsetEquiv cs J I).map subtype_J),
```

where `w` acts by `weylCharacterAction i hN hZ (longestRep cs J)` and
`K = associatedSubset cs J`. The proof obtains positivity and simple-image
membership for each label in `I`, then applies the published comparisons
between actual root images and simple-reflection images, together with
`simpleImage_associatedFinsetEquiv`.
Empty subsets and empty simple-label types require no separate assumption.
Third, `associatedRootSetEquiv` restricts the lattice automorphism to its
set image and then uses the proved set equality. Its application lemma
records that the resulting map is exactly that lattice automorphism.

`weylAction_image_associatedFinsetEquiv` rewrites the quotient action as
the actual scheme-normalizer action for every point-normalizer lift `n`
whose class is `longestRep cs J`. It uses the representative-preserving
`normalizerEquiv` and the published `weylCharacterAction_point_mk`.

The provenance is internal and derived from `RationalRootSignTarget`,
`RationalWeylRootAction` and `RelativeWeylAssociatedIndexing`. This is the
finite-subset companion of the published `rootSet_associatedSubset`.
Workers 76 and 165 identified the need to retain the weaker point Coxeter
data in the associated-Levi consumer. No external structure theorem is
invoked in this unit. The results identify actual character sets; they
prove no equality of parabolic, Levi or unipotent subgroup functors and no
representation transport. Those structural and consumer obligations
remain separate.
