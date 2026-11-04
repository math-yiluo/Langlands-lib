# Positive central cocharacters and actual split components

This is derived infrastructure for the minimal-parabolic Levi-centralizer
proof. It combines the published integral Galois orbit sum, pairing invariance,
actual cocharacter descent, all-test central descent and integral
split-component factorization. It introduces no geometric existence theorem.

Let `k` and `K` be fields in the same arbitrary universe `u`, with a `k`-algebra
structure on `K` and a finite enumeration of its `k`-automorphism group. Let
`T` be any commutative group scheme over `Spec k`, and write `T_K` for its actual
scheme base change. Let `Φ` be a family of characters of `T_K` preserved by
the canonical Galois action. Suppose every member pairs strictly positively
with an actual integral cocharacter `ν` of `T_K`.

`CocharacterAveraging.latticePairing_galoisOrbitSum_pos` proves that every member
of `Φ` also pairs strictly positively with the integral Galois orbit sum of
`ν`. Pairing invariance moves each Galois translate of `ν` to the inverse
translate of the character. Stability and the given positivity make each
summand positive. The automorphism group contains its identity, so the finite
sum is strictly positive. No division, rationalization, finiteness of `Φ`,
nonemptiness of `Φ` or assumption on its zero character is required.

For the remaining results, assume `K/k` is finite-dimensional and Galois,
and the structure morphism of `T` is affine.
`CocharacterAveraging.latticePairing_baseChange_descendedOrbitSum_pos` uses
the published exact base-change identity for the descended orbit sum to give
the same positivity after extending that actual cocharacter over `k`.

Let `t : T → M` be an actual homomorphism to any group scheme over `k`. If the
composite of `ν` with `t_K` is central on every test scheme,
`exists_centralCocharacter_positive_of_galois_stable` exhibits an actual
cocharacter of `T` central in `M`, whose base change is positive on all of `Φ`.
Its witness is the published descended integral orbit sum. Centrality is the
published all-test central descent theorem. This step requires no smoothness,
connectedness, reductivity or affineness of `M`.

Now additionally assume `M` has affine structure morphism and the underlying
scheme map of `t` is monic. Let `a : A → M` be a specified split component,
and supply a lift `f : A → T` with `groupHom f ≫ t = a`.
`IsSplitComponent.exists_positiveCocharacter_factor` constructs an actual
integral cocharacter `ζ` of `A` whose image in the cocharacter lattice of `T`
equals the descended orbit sum. Its image remains strictly positive on `Φ`
after base change. The proof uses the published equality between the range of
the integral cocharacter map of `f` and the submodule of cocharacters central
in `M`. Thus the conclusion concerns the supplied morphisms and an actual
integral factorization, rather than an abstract vector-space representative.

`IsSplitComponent.positiveCocharacterFactor` chooses such an actual integral
cocharacter of the specified `A` from the existence theorem.
`IsSplitComponent.positiveCocharacterFactor_spec` proves both its exact
factorization equality and the strict positivity of its extended image.
The definition uses classical choice; no uniqueness of the factor is claimed.

`IsSplitComponent.characterRestriction_ne_zero_of_central_positive` proves
that every member of `Φ` has nonzero character restriction along `f_K`.
If a restriction were zero, the published split-component pairing theorem
would make its pairing with the central Galois orbit sum zero, contradicting
the strict positivity above.

The character-family stability, initial positive central cocharacter, finite
Galois extension, specified split component and specified lift remain inputs.
This module does not establish Galois invariance for an arbitrary subgroup
functor, construct a central positive direction from geometric hypotheses,
or prove the ambient maximal-split Levi-centralizer statement.
