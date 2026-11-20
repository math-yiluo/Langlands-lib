# Transfer of natural cocycles through affine Weil restriction

Let `A` and `B` be commutative rings in an arbitrary common universe, with `B` a finite projective `A`-algebra. Let `H` be a group scheme over `Spec B` with affine underlying scheme and locally finite-type structure morphism. The restriction is `Langlands.GroupScheme.AffineWeil.groupScheme A B H`.

`cocycleEvaluation` is the group morphism from the base change of this restriction to `H`. For a natural cocycle on an arbitrary cover object over `Spec A`, `transferCocycle` pulls the cocycle up to `Spec B` and applies this morphism. Its cover is the scheme pullback of the original cover.

The construction uses the counit of affine Weil restriction. On standard affine tests, its comparison on points agrees with the multiplicative tensor-algebra comparison. The same identity on arbitrary affine tests follows by an affine chart. The product of the Weil restriction with itself is affine, so the universal pair of points gives the multiplication identity for every test scheme. The pullback adjunction and the natural correspondence between group morphisms and maps on points give `cocycleEvaluation`.

`isTrivial_of_transferCocycle` reflects a trivialization when the original cover is affine. The Weil comparison on the cover recovers the cochain from its transferred value. Naturality and injectivity of the comparison on the double overlap give the coboundary identity for this cochain. This is an internal comparison for the number-field Hasse kernel.
