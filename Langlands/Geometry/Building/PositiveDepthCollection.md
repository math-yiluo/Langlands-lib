# Collection at arbitrary depths on closed positive root sets

This internal construction works over any field in universe u. It takes a
monomorphic torus map i into an affine group scheme, a root-function family φ,
and an actual `IsRootDatumValuation i φ`. It does not take an apartment, an
affine root system, or a derivative comparison.

`IsClosedPositiveRootDepth i ν Ψ f` records the exact root and depth conditions
used here. The set Ψ is contained in the actual roots positive on ν. Whenever
a and b lie in Ψ, p and q are positive natural numbers, and p*a + q*b is an
actual relative root, that root also lies in Ψ and its real depth satisfies
f(p*a + q*b) ≤ p*f(a) + q*f(b). The conditions include a = b and retain
all actual doubled roots. The function f may have arbitrary real values;
positivity is required of root pairings with ν, not of the depths. This
explicit condition is the hypothesis of the construction; no general
equivalence with another definition of concavity is asserted.

For any complete finite enumeration a of Ψ, `positiveDepthProductSubgroup`
has as its carrier the actual ordered-product set
`orderedRootFiltrationProduct i φ a (f ∘ a)`. Subgroup structure is proved.
Its equality with the supremum of all original filtration subgroups over Ψ,
and with the closure of the union of their actual filtration sets, retains
the original group, valuation and real bounds. The enumeration may contain
repetitions and may be empty. No injectivity of the ordered product is needed.
The range is independent of the complete enumeration and its ordering.

The proof first rewrites V3 using the existing actual filtration subgroups
from V1. It removes closures of subgroup carriers and rewrites the closure
of a union as a subgroup supremum. Positive roots are nonopposite, and every
positive integral root combination has pairing height strictly greater than
both inputs. The explicit depth inequality and antitonicity of filtration
subgroups place each V3 output in its original subgroup at depth f. Thus
commutators strictly increase the two natural-number pairing heights.
`HeightCollection.range_orderedProduct_eq_iSup` gives collection in the supplied
finite order, without requiring that order to sort the heights. A carrier
copy supplies the subgroup whose literal membership condition is existence
of the ordered factorization. Both enumeration independence and the closure
identity follow from the common subgroup supremum.

The provenance is internal composition of the published valuation axioms,
the actual filtration-subgroup construction, the positive-pairing calculations
in `ChamberPositiveCollection`, and the finite group theorem in
`GroupTheory.HeightCollection`. No new assertion from external literature is
used. In contrast with the earlier zero-depth chamber result, this argument
works at arbitrary real depths on a supplied closed positive subset directly
from a valuation. It neither compresses doubled-root factors into indivisible
root positions nor descends the subgroup under field extension. Establishing
V3 for a restricted family, constructing an actual valuation or apartment, and
proving the host building comparison remain separate obligations.
