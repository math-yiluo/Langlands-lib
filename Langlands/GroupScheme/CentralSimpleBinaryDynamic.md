# Actual contracting cocharacters in the canonical binary norm-one group

This is an internal construction from the published finite-algebra binary cocharacters and contraction curves, the canonical binary tensor norm, and the actual norm-one kernel lifting interface in `CentralSimpleBinaryRoots`. Let `k : Type u` be any field and `D : Type u` any finite-dimensional central simple `k`-algebra. The coefficient ring `D` may be noncommutative. No local-field or characteristic restriction is imposed.

The ambient group is the actual canonical group scheme `CentralSimpleUnits.normOne k (Matrix (Fin 2) (Fin 2) D)`. Its inclusion `normOneι` goes to the actual unit group scheme of the binary matrix algebra. The fixed `matrixBasis k D` is `Module.finBasis` of that matrix algebra and only supplies coordinates for the published point equivalence.

## Cocharacters

The Boolean `neg` selects the upper elementary family when false and the lower family when true. `contractingMatrix_tensorNorm` proves that the scalar diagonal matrix has canonical tensor norm one on every commutative `k`-algebra `R`. For the upper orientation its entries are the images of a unit `t : Rˣ` and its inverse in `R tensor_k D`; for the lower orientation their order is reversed. The proof uses `BinaryNorm.tensorNorm_diagonal_inverse`, at the scalar unit or its inverse, and the fact that a unit homomorphism preserves inverses.

`cocharacter_tensorNorm` applies this identity to the exact all-test matrix formula for the published full-unit cocharacter. `cocharacter` then applies `liftHom` to obtain an actual ground-field morphism of group schemes from `Gm` into the canonical norm-one group. Its source is the base field, not a splitting extension. `cocharacter_ι` identifies its composite with the actual kernel inclusion with the original scalar-diagonal cocharacter. This construction does not require a choice of basis for `D`.

## Curves and contraction

Fix any finite basis `bD : Module.Basis (Fin d) k D`. For any relative test scheme `T` over `Spec k` and any point `x` of the actual additive vector group of dimension `d`, `contraction_tensorNorm` proves that the published elementary polynomial curve on `T × A¹` has tensor norm one. Its tensor parameter is `s²a`, with `a` the tensor coordinate of `x`, pulled back from `T`, and `s` the affine-line coordinate. The proof uses the upper or lower tensor-norm identity for that entire parameter, so it proves the kernel condition for the whole polynomial curve, including zero.

`contraction` lifts this actual curve through the kernel using `liftPoint`. `contraction_ι` gives its exact factorization through the inclusion. `contraction_isOrbitExtension` proves that the lifted curve restricts on `T × Gm` to conjugation of the corresponding norm-one elementary point by the lifted cocharacter. The proof cancels the monomorphic norm-one inclusion, transports the orbit using `Dynamic.orbit_comp_hom`, and applies the already proved full-unit orbit-extension identity. `contraction_evalZero` similarly uses `Dynamic.evalZero_comp` and cancellation to transport the full-unit identity at zero.

Finally, `elementary_range_le_dynamicUnipotent` proves containment of the whole subgroup-functor image of the actual elementary map in the dynamic unipotent functor of the corresponding actual norm-one cocharacter. On every relative test scheme, any point of that image has a preimage `x`, and the constructed curve supplies the orbit-extension and identity-at-zero witnesses required by `Dynamic.unipotent`. This is an all-test statement, not just a statement about rational points.

## Scope

All definitions and identities are derived internally from actual published schemes and morphisms. The construction supplies norm-one cocharacters and elementary contraction curves and proves dynamic containment. Identification with geometric radicals of actual parabolics, generation of the full norm-one rational group, local SK1 vanishing, classification of general local groups, and the unrestricted `LocalKneserTitsStatement` remain separate obligations.
