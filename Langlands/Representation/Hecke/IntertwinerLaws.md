# Equal original maps and integrated Hecke intertwiners

This is internal infrastructure for `Langlands.Hecke.heckeActionIntertwiner`.
The group is a topological group with its Borel measurable structure. Its measure
is left invariant and finite on compact sets. The complex module carriers have
independent universes, and the group representations are smooth.

`heckeActionIntertwiner_id_of_eq` takes an original group intertwiner equal to
the identity and identifies its integrated Hecke intertwiner with the identity.
`heckeActionIntertwiner_comp_of_eq` takes three original group intertwiners
`T`, `U`, and `TU`, together with `TU = U.comp T`, and identifies the integrated
map for `TU` with the composite of the maps for `T` and `U`, in that order.
Both proofs substitute the given equality and apply the existing identity or
composition law for `heckeActionIntertwiner`.

The construction retains the original linear maps and the same measure.
These equality helpers assert no converse from integrated equivariance to group
equivariance and no existence or normalization result.
