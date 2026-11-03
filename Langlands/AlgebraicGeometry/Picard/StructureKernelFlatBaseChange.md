# Flat base change of the actual structure-map kernel module

This internal construction uses the published actual structure-map kernel
module, canonical structure-module pullback comparisons, affine pushforward
base change, and exactness of flat module pullback. It has no new external
source input. All schemes lie in an arbitrary universe `u`.

For a commuting square `p ≫ i = i' ≫ b`, `pullbackSquare_unit` identifies
the two composites of canonical pullback comparisons for the actual
structure modules. `structurePushforwardBaseChange` is the published
adjunction-defined pushforward base-change map for the structure module,
followed by pushforward of the canonical identification of its pullback
with the new structure module. `structureMap_baseChange` proves that the
pullback of the actual structure map `O_X → i_* O_Y` followed by this
comparison is the canonical identification `b^* O_X → O_X'` followed by
the actual new structure map `O_X' → i'_* O_Y'`.

When the square is cartesian and `i` is affine, the published affine
pushforward base-change isomorphism makes this comparison an isomorphism.
When `b` is flat, the published exactness theorem says that `b^*` preserves
kernels. Transporting the actual kernel module through its published
categorical-kernel identification, this preservation isomorphism, and
the commuting square of structure-module isomorphisms yields

```text
kernelModuleFlatBaseChangeIso :
  b^*(StructureKernelModule.kernelModule i) ≅
    StructureKernelModule.kernelModule i'.
```

The object on each side uses the actual sectionwise kernel of the scheme
structure map, with its actual module action. No square-zero, nilpotence,
compactness, noetherian, or splitting hypothesis is needed. The construction
does not identify the cohomology base-change maps, the multiplicative unit
boundaries, or the Picard lifting fibres under this isomorphism.
