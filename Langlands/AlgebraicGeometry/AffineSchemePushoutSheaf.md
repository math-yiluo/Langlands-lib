# Structure sheaves of an affine ring pullback

This is an internal construction for the affine scheme pushout proof. Let
`f : B →+* D` and `g : C →+* D` be arbitrary homomorphisms of commutative rings,
and let `P = f.pullback g`, with projections `i` and `j`. All rings lie in the
same arbitrary universe. No surjectivity or nontriviality hypothesis is needed
for this construction.

`overSheaf i` is the structure sheaf on `Spec B`, pushed onto `Spec P` along
the map induced by `i`. The analogous sheaves for `C` and `D` use `j` and
`k = f.comp i`. `overSheafMap` maps sections on inverse images of opens using
`StructureSheaf.comap`. Its compatibility hypothesis identifies the composite
ring map with the specified map from the base ring. The composition law follows
from the composition law for these section maps. The section rings carry their
canonical algebras over the respective factor rings, and
`comap_comp_algebraMap` proves the corresponding scalar compatibility.

`overSheafInl` and `overSheafInr` are the section maps of the spectrum
projections. `overSheafFst` and `overSheafSnd` map the two pushed sheaves to the
common pushed sheaf. `overSheaf_square` proves their commutativity, using the
original pullback equality `f.comp i = g.comp j`.

On a basic open defined by a compatible pair `a : P`, the four section rings
are localizations away from `a`, its two coordinates, and their common image
in `D`. `isPullback_basicOpen` applies
`AffineSchemePushout.isPullback_localization` with the actual section maps and
the proved scalar compatibilities. It establishes the categorical pullback
square in `CommRingCat` on each such basic open.

`sheafPullbackComparison` is the canonical morphism from the structure sheaf
of `Spec P` to the categorical pullback of the three pushed sheaves. Forgetting
sheafness and evaluating at an open preserve limits. On each basic open, the
comparison is therefore the isomorphism between the two pullback objects from
the preceding paragraph. The sheaf basis criterion, applied to the basis of
prime-spectrum basic opens, proves that this comparison is an isomorphism of
sheaves. Transporting the canonical pullback along it gives
`isPullback_overSheaf`; `isPullback_overPresheaf` forgets sheafness.

The construction is derived from the localization helper and Mathlib's
structure-sheaf maps, uniqueness of pullbacks, preservation of sheaf limits,
and the basis criterion for a sheaf isomorphism. It supplies the sheaf part of
the affine pushout argument; the topological and scheme universal properties
are further steps.
