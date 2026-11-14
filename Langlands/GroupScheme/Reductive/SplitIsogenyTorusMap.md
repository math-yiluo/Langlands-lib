# The actual torus map of a root-datum isogeny

This is a derived construction for the general split isogeny theorem. It does
not assert general realization of noncentral root-datum isogenies.

All declarations are in `Langlands.GroupScheme.RootDatumIsogenyRealization`.
Over any field, let `P` and `P'` be finite reduced root data on the actual
character and cocharacter lattices of commutative group schemes `T` and `T'`,
with all four lattices finitely generated. Let `f : RootDatumIsogeny p P' P`.
The exponent `p` can be any characteristic exponent permitted by that type.
The root indexing types and the field lie in the same arbitrary universe.

`torusMap hT' f` is the actual morphism `T → T'` constructed by split-torus
character duality from `f.weightMap`. Only the target torus must be split for
this construction. `torusMap_comp` gives its character pullback, and
`eq_torusMap` proves uniqueness from that equation.

When the root-datum pairings equal the actual torus pairings,
`coweightMap_apply_of_weightMap` shows that any torus map inducing the weight
map also induces the coweight map. Its proof evaluates the transpose equation
and uses the injectivity of the perfect pairing of `P'`. It applies to general
characteristic-power root factors. `comp_torusMap` specializes it to the
constructed map. If both tori are split, `torusMap_isIsogeny` applies the
published split-torus isogeny criterion to the injectivity of both lattice
maps. The conclusion means finite, flat and surjective on actual schemes.

`exists_central_realization` further assumes connected reductive ambient groups,
split maximal-torus inclusions, and that the given root data are their actual
root data. If every root factor of `f` is one, it uses `f.toHom` and the
published `splitCentralIsogenyExistence` theorem. Character extensionality
identifies the resulting torus map with `torusMap`. This proves realization
by a central group isogeny together with a torus isogeny and both actual
lattice equations. No smoothness assumption is placed on either kernel.
`exists_realization_expChar_one` applies this construction because all powers
of one equal one. These are central special cases, not the full positive
characteristic realization assertion.

The provenance is derived from the published character-duality, perfect-pairing,
split-torus isogeny and central realization results imported by the Lean module.
The construction follows the direction conventions of `SplitIsogenyStatement`:
weights map from `X(T')` to `X(T)` and coweights from `Y(T)` to `Y(T')`.
