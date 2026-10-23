# Idele-class invariants represented in a chosen extension

This internal construction uses the actual idele-class inflation and quotient
cohomology maps. All fields have an arbitrary common universe. For a scalar
tower `F → E → L`, write `j_L` for the map from
`H²(Gal(L/F), J_L)` to `H²(Gal(L/F), C_L)`.

`ideleClassRegularSubgroup F E L` is the inverse image of `range(j_L)` under
inflation from `H²(Gal(E/F), C_E)` to `H²(Gal(L/F), C_L)`. Membership says
exactly that there is an idele cohomology class `a` over `L/F` with
`j_L(a) = Inf(c)`. The subgroup and its map `ideleClassRegularInflation`
require a field `F`, number fields `E` and `L`, a scalar tower, and `E/F`
Galois. They do not require `F` to be a number field or `L/F` to be Galois.
The subgroup contains the image of the quotient cohomology map over `E/F`,
because the actual quotient map commutes with inflation.

For the invariant construction, assume additionally that `F` is a number
field and `L/F` is Galois. Supply a local invariant family `I` with
`RelativeImages` at every prime, one finite and one infinite place of `L`
over each corresponding place of `F`, and the explicit hypothesis that
`Reciprocity.SumOfInvariantsVanishes I x` holds for every field-unit class
`x` over `L/F`. Then `ideleClassInvariantViaExtension` is an additive map
from this subgroup to `ℚ/ℤ`: inflate into `range(j_L)`, then apply
`ideleClassInvariantOnQuotientRange` with the supplied places and reciprocity
proof. If `a` represents the inflated class, its value is exactly
`totalIdeleInvariant I hI wf wi a`, for every such representative.

For four number fields forming a compatible tower `F → E → L → M`, with
`E/F`, `L/F`, and `M/F` Galois, `ideleClassRegularSubgroup_le` proves that
the subgroup defined using `L` is contained in that defined using `M`.
The proof uses transitivity of actual idele-class inflation and preservation
of the quotient-map image under inflation.
`ideleClassInvariantViaExtension_tower` identifies the two invariant values
on this inclusion. It requires the supplied family's `InflationCompatibility`
law, reciprocity over both `L/F` and `M/F`, and compatible finite and infinite
place choices: each selected place of `M` lies over, or has comap equal to,
the selected place of `L`. Transitivity identifies the range-valued
inflation maps, and the range invariant's inflation theorem gives the result.

The final comparison theorem uses two number fields `L₁` and `L₂` inside a
supplied common number field `M`, all Galois over the same number field `F`,
with the two scalar triangles. If the quotient images of idele classes
`a` over `L₁/F` and `b` over `L₂/F` become equal after inflation to `M/F`,
then their total invariants are equal. Here `RelativeImages` and
`InflationCompatibility` are assumed for `I`; reciprocity is needed only
over `M/F`. Each of the two lower systems of finite/infinite places must
be compatible with the same upper system in `M`. The proof inflates both
representatives, uses the two quotient/inflation squares, applies equality
of total invariants for equal quotient images in `M`, and uses preservation
of total invariants under inflation twice.

The provenance is internal: subgroup inverse images, the actual tower laws
from `CohomologyTowerProof` and `IdeleCohomologyTower`, and the conditional
range invariant from `IdeleTotalTower` supply all the constructions and
proofs. This pair treats a specified representing extension or a specified
common overfield. It does not construct a common overfield, assert
independence from unrelated place choices, or prove that every idele-class
cohomology class becomes represented after inflation. It does not prove
`GlobalInvariantStatement`.
