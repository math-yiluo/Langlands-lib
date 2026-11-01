# Concrete exactness criteria for nondegenerate modules

These intrinsic helper lemmas express categorical exactness as the existence of
preimages of elements in the kernel, monomorphisms as injective additive maps,
and epimorphisms as surjective additive maps. They apply to the actual full
category of nondegenerate modules, at independent ring and carrier universes.

The exactness criterion uses the published exact inclusion into the ambient
nonunital module category and its range/kernel criterion. The monomorphism
criterion uses the published inclusion and ambient injectivity criterion. For
epimorphisms, the proof uses the published exact inclusion, the actual integer
unitization equivalence, and Mathlib's surjectivity criterion in ModuleCat.
All three use the named abelian structure on the original nondegenerate category.
These are derived proof tools for Renard I.2.4 rather than new source assertions.
