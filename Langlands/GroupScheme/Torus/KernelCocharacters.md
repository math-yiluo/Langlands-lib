# Actual-kernel Hom groups and cocharacters

This internal construction uses the published pullback kernel and its natural identification on every scheme of points. For a homomorphism `f : G → H` of commutative group schemes over an arbitrary scheme `S`, `CommGroupScheme.kernel f` is that actual pullback kernel with inherited commutativity, and `kernelι f` is its actual inclusion.

The pointwise kernel equivalence lifts a homomorphism `g : P → G` with `g ≫ f = 0` to an actual homomorphism `P → kernel f`. Naturality is proved by the monomorphism of the actual inclusion, and the published Yoneda construction produces the morphism. Its composite with inclusion is `g`, and inclusion determines any such factor uniquely.

`CommGroupScheme.postcompose f P` is the additive map on actual Hom groups given by composition with `f`. `kernelHomEquiv f P` identifies the actual Hom group into the kernel with the kernel subgroup of this additive map, and preserves addition. Specializing `P` to the multiplicative group gives `cocharacterLattice.kernelEquiv`; its underlying cocharacter is exactly composition with the inclusion.

No smoothness, reducedness, finiteness, field, torus or quotient hypothesis is imposed. All pointwise arguments use arbitrary test schemes. The definitions are derived from existing kernel and lattice constructions; this file neither assumes nor proves character exactness, a norm-one coordinate comparison or a Galois-action formula.
