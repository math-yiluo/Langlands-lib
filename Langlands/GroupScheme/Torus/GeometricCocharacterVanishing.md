# Geometric vanishing of commutative cocharacters

This internal deduction extends finite-Galois cocharacter vanishing to the
algebraic closure. It uses the actual group-scheme pullback and actual
homomorphisms from the multiplicative group.

`CommutativeGeometricCocharacterVanishingStatement` quantifies over an arbitrary
field `k : Type u` and an affine commutative group scheme `Z` locally of finite
type over `k`. If every homomorphism from every `k`-torus to `Z` has bottom
subgroup-functor range, every cocharacter of `Z` over `AlgebraicClosure k` is
zero. Neither smoothness nor connectedness of `Z` is assumed.

The implemented proof represents a cocharacter by its multiplicative universal
point with coefficients in the group algebra of `PUnit → ℤ`.
The algebraic closure is purely inseparable over `SeparableClosure k`.
`IsMult.exists_coeffMap_eq_of_isPurelyInseparable` therefore descends the exact
point to the separable closure, with equality after coefficient extension.
The separable closure is Galois over `k`, so
`multiplicativePoint_eq_one_of_isGalois` makes that descended point the identity.
Coefficient extension gives the same conclusion over the algebraic closure.
The zero comparison and injectivity of `gmHomEquivMultiplicativePoints` then
give equality of the actual cocharacter with zero.

`multiplicativePoint_eq_one_over_algebraicClosure` records the point argument,
`gm_hom_eq_zero_over_algebraicClosure` records its actual-morphism consequence,
and `commutativeGeometricCocharacterVanishing` proves the named proposition.

This uses the coefficient descent and actual finite-Galois Weil-transfer
infrastructure from `CocharacterPurelyInseparableDescent`,
`CocharacterBaseChange`, and `CocharacterFiniteGaloisDescent`. It does not assume
that the no-torus hypothesis itself survives base change. This supporting result
does not prove the general noncommutative `NoTorusUnipotentStatement`.
