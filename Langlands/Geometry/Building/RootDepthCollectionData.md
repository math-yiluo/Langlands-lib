# Filtration subgroup data for positive-depth collection

This internal unit isolates the actual inputs used by positive-depth collection.
It works over any field at universe `u`, with an affine ambient group scheme;
no monomorphism premise is required by this interface.
`RootDepthCollectionData i φ` consists of subgroups whose literal carriers are
`rootFiltration i φ a r`, the V3 inclusion between these subgroups, and the
arbitrary-depth doubled-root inclusion when `2 * r ≤ s`. The V3 condition uses
the original actual root set and the original nonopposite real-ray condition.
There are no reflection, opposite-root, support-normalization, nontriviality,
or apartment-existence fields. The data must be supplied; this unit does not
assert their existence for a new class of groups.

Carrier equality gives antitonicity in the real depth and containment in the
actual root group. `selectedDepthSubgroup` assigns the identity subgroup at an
unselected character. `rayDepthSubgroup` retains the primitive filtration when
selected, otherwise the doubled-root filtration at its original depth when
selected, otherwise the identity subgroup. `orderedRayDepthProduct` is the
literal set of ordered products of these actual subgroups.

For `IsClosedPositiveRootDepth i ν Ψ f`, the V3 inclusion and the supplied
combination-depth bound force commutators to have strictly larger positive-root
height than both inputs. The generic height-collection theorem then identifies
the ordered product over any finite list covering the selected roots with the
supremum of their filtration subgroups. Repetitions and extra unselected entries
are allowed. This uses no root-datum valuation beyond the displayed data.

If the list covers every selected root by a primitive or doubled entry, insert
two positions for every ray. Collect over this longer list, then combine each
adjacent pair of comparable subgroups. The supplied doubled-root depth bound
absorbs the doubled factor when both roots are selected. If only the doubled
root is selected, it remains as the actual factor at its original depth. If
neither is selected, the factor is the identity. The resulting
`orderedRayDepthProduct_eq_iSup` retains all real depths, including negative
ones. `orderedRayDepthProduct_eq_closure` identifies this product with the
subgroup closure of the union of the original actual filtration sets.

The proof extracts the height-collection and adjacent-comparable-pair arguments
from the existing `PositiveDepthCollection` and `PositiveDepthRayCompression`
interfaces. These are internal group-theoretic consequences; no additional
literature theorem is claimed. In particular, no full valuation, its reflection
or opposite-root laws, or the host supplied-model building comparison is
constructed by this unit.

The generic adjacent-pair theorem `range_orderedProduct_rayPairs` is reused from `PositiveDepthRayCompression` with its unchanged statement.
