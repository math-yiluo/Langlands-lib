# The ordered cell in the generic Chevalley closure

This internal construction applies generic ordered-cell descent to the fixed
flat schematic closure of a supplied generic Chevalley group over a Dedekind
domain. The root datum is reduced and its character lattice is finitely
generated.

A flat morphism from `W` to the closure makes `W` flat over the base. Its
pullback to the fraction field followed by the specified generic
identification is flat. The generic compatibility of the model inclusion
and the general-linear base-change comparison give the exact matrix
compatibility required by `GenericCellDescent`. Consequently a compatible
map from `W` to the ambient matrix cell factors through the full ordered
parameter product. `closureCellFactor` chooses this actual parameter map
and its companion theorem proves the factorization identity.

This is derived from the existing generic model, its generic matrix
compatibility, stability of flatness and the schematic descent construction.
