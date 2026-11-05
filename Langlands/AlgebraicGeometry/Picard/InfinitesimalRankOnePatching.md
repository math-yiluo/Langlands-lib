# Free rank-one patching across an infinitesimal ring square

This internal construction concerns actual commutative rings in an arbitrary
common universe and an actual categorical pullback square
`R → A`, `R → B`, `A → C`, `B → C`. It is a focused prerequisite for
Picard infinitesimal gluing, not a proof of the actual scheme-groupoid comparison.

The underlying-set pullback supplies lifts of compatible pairs and joint
injectivity of the two projections. In particular, surjectivity of `B → C`
implies surjectivity of `R → A`. Compatible units patch uniquely by patching
their values and inverses and checking both inverse laws by joint injectivity.

For a specified overlap unit `c : Cˣ`, the module `patchedModule` consists of
actual pairs `(x,y)` satisfying `a x = c * b y`, with the action of `R`
through its two projections. Given an actual unit `v : Bˣ` mapping to `c`,
`frameEquiv` is the linear equivalence sending `r` to
`(p r, v⁻¹ * q r)`. Its bijectivity follows by applying the ring pullback
to the compatible pair `(x,v*y)`. The two projection formulas retain the
specified multiplier and the unit lift. The published nilpotent unit-lifting
theorem supplies such a `v` when `B → C` is surjective with nilpotent kernel;
`exists_frame` records the equivalence and both projection formulas.

The module portion uses `Algebra R A` and `Algebra R B`, so its two
projections are their actual algebra maps. Arbitrary ring maps `p` and `q`
fit this interface by using their induced algebra structures.

For overlap units `c,d` and scalars `x : A`, `y : B` satisfying
`a(x)*c = d*b(y)`, `diagonalMap` sends `(z,w)` to `(x*z,y*w)`.
Its projection formulas and `diagonalMap_unique` give the unique map with
those specified projections. For actual units `x,y` satisfying the same
compatibility in `Cˣ`, `diagonalEquiv` is the corresponding linear
equivalence. Compatibility of the inverse multipliers follows by
multiplying the original equality by the two inverse units. The inverse
acts by those inverse multipliers, and both inverse laws follow
componentwise. The same projection uniqueness proves
`diagonalEquiv_unique`. Thus these constructions preserve the supplied
overlap units and component isomorphisms.

The proof is derived directly from Mathlib's preservation of ring pullbacks
by the forgetful functor, its underlying-set pullback lemmas, elementary
ring and module identities, and the published `NilpotentUnitReduction` unit
lifting theorem. No external mathematical assertion is an additional input.
This does not yet construct scalar-extension identifications, patch arbitrary
projective modules, glue global line bundles, or prove that the actual
`PicardGroupoid.affineSquareComparison` is an equivalence. Those remain
obligations for the exact infinitesimal-gluing proof and representability.
