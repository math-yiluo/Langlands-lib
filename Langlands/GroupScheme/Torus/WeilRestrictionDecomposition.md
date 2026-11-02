# Splitting Weil restriction from an algebra decomposition

This internal adapter combines the existing Weil restriction base-change,
algebra-transport, and finite-product splitting isomorphisms. For commutative
rings `A`, `A'`, a finite projective commutative `A`-algebra `B`, a finite type
`I`, and a specified `A'`-algebra equivalence
`e : A' ⊗[A] B ≃ₐ[A'] (I → A')`, `decompositionIso` identifies the actual base
change of `WeilGm.groupScheme A B` with `splitTorus (Spec A') I`.
`commDecompositionIso` gives the same composite in `CommGroupScheme`.

`decompositionTensorEquiv` is the corresponding ring equivalence on any
`A'`-algebra `R`, with its compatible `A`-algebra structure. It sends
`b ⊗ r` to the family `i ↦ e (1 ⊗ b) i • r`. This purely algebraic
construction only requires `I` finite, without finite projectivity of `B`.

`decompositionPointsEquiv` identifies points on every test scheme `T` with
families of global units. Its formula applies the published base-change
tensor equivalence, `e ⊗ id`, the product-algebra tensor equivalence, and the
coordinate equivalence for product units. `commDecompositionIso_hom_points`
identifies this explicit map with the actual scheme isomorphism, and
`decompositionPointsEquiv_naturality` proves compatibility with every map of
test schemes, including nonreduced tests.

Over a field `K` in the place of `A'`, `decompositionCharacterEquiv` and
`decompositionCocharacterEquiv` identify the actual lattices of the base
change with `I → ℤ`, by transporting the published split-torus lattice
coordinates along this splitting. `decomposition_latticePairing_eq_sum`
identifies their pairing with the dot product, and
`decomposition_latticePairing_isPerfPair` proves that this pairing is
perfect. The latter explicitly takes the decomposition `e` as a parameter:
it does not assert perfectness without a supplied splitting. Both
lattice equivalences use the same order of coordinates in `e`.

`decompositionCharacterEquiv_symm_points` says that the character
corresponding to `m : I → ℤ` sends a point with decomposition coordinates
`z` to `∏ i, z i ^ m i`. This finite product uses a `Fintype I` instance.
`decompositionCocharacterEquiv_symm_points` says that the corresponding
cocharacter sends a global unit `s` to the coordinates `i ↦ s ^ m i`.
These formulas hold on all test schemes. The `_symm_eq` lemmas record
the actual morphism composites defining these inverse lattice maps.

These are intrinsic consequences of the specified algebra decomposition
and the existing modules `WeilRestrictionBaseChange`,
`WeilRestrictionSplit`, `WeilRestrictionCommutative`, `Lattice`, and
`LatticeGalois`. The module does not construct the input decomposition,
prove it exists for every finite separable extension, or assert a Galois
equivariance or continuity theorem. Those are separate obligations.
