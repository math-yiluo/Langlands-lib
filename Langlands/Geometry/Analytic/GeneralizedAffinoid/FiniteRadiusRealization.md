# Simultaneous radius realization for finite chart families

Author: Worker 146.

This internal construction extends the indexing interface of the published
`RadiusRealization`. The coefficient field is in `Type u`, while the finite
family of prescribed radii may be indexed by a type in an independent
`Type v`. The extension field remains in `Type u`.

`FiniteRadiusRealization K t` contains a complete ultrametric normed field
`L`, an isometric ring embedding `ι : K →+* L`, elements `c i` with
`‖c i‖ = t i`, and a bounded additive retraction `π : L →+ K`.
The retraction satisfies `π (ι a * x) = a * π x` and `π 1 = 1`.
Its norm bound is a positive real number. The structure itself imposes no
finiteness or positivity assumptions; its existence theorem does.

`FiniteRadiusRealization.nonempty` supplies the structure for any finite
index type and any family of positive real numbers. It enumerates the index
type by `Fin (Fintype.card σ)`, invokes the existing
`RadiusRealization.nonempty`, and reindexes its chosen elements. No change
to the extension field is necessary. `c_ne_zero` follows from positivity
and the prescribed norm.

For a family `D` of actual rational charts over a presented affinoid
algebra `A`, `FamilyRadiusIndex D` is the disjoint union of the base
coordinates and all chart coordinates. The function `familyRadius D`
assigns the base polyradius on the first summand and the chart's relative
radius on the second. Every value is positive. For finite `I`,
`familyRadiusRealization_nonempty` realizes all these radii in one field
in `Type u`. Empty base tuples, empty chart tuples, and empty chart families
are included.

This is derived indexing infrastructure for strictification. Its analytic
input is precisely the imported finite radius realization theorem. It
constructs no rational quotient transport and proves no affinoid descent
claim.
