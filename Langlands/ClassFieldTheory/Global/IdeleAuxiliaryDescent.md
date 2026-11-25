# Conditional descent along a cyclic auxiliary tower

This supporting module implements the descent step of Artin–Tate,
*Class Field Theory* (2009), Chapter VII §3, printed p.50. It uses the
actual idele-class cohomology, its regular subgroup, and its published
inflation and restriction maps. All fields have an arbitrary common
universe. The arithmetic inputs and the regular invariant homomorphisms
are explicit hypotheses; this module does not construct the global
invariant family or prove `GlobalInvariantStatement`.

Let `E/F` be a Galois extension of number fields, of degree `n`. Supply
a `CyclicAuxiliaryTower F E n`, with auxiliary field `K/F` cyclic of
degree `n` and common Galois overfield `L/F` such that `L/E` is cyclic.
Also supply additive maps `sE`, `sK`, `sL`, and `sUpper` to the rationals
modulo integers from the actual regular subgroups for `E/F`, `K/F`,
`L/F`, and `L/E`. The descent hypotheses are:

- Inflation preserves the supplied maps from `E/F` and `K/F` to `L/F`.
- Restriction from `L/F` to `L/E` multiplies their values by `n`.
- The upper map `sUpper` is injective.
- The range of `sK` is the denominator subgroup for `[K:F]`.
- The published Galois descent proposition holds, and the actual
  relative `H¹(Gal(L/E), C_L)` is a subsingleton.

The tower's cyclicity explains how the upper injectivity and auxiliary
range are expected to be provided by the cyclic case. The proof below
uses those two consequences explicitly; it does not deduce them merely
from cyclicity.

First, `regularIdeleClassInvariant_mem_denominator` proves that any
additive map from the regular subgroup for `E/F` takes values in the
`n`-denominator subgroup. The group order kills actual `H²`, hence its
regular subgroup, and an additive map preserves this annihilation.
`regularIdeleClassInvariantToDenominator` corestricts the map accordingly.
Neither result assumes that the cohomology group is finite.

For any denominator value `y`, the auxiliary range hypothesis gives a
regular class over `K/F` with value `y`. Inflate it to `L/F`. Its
restriction to `L/E` has value `n • y = 0`, so upper injectivity makes
that restriction zero. `ideleClassH2InflationExactness_of` supplies a
class over `E/F` whose inflation is the chosen class over `L/F`.
The already proved reflection of regularity under inflation makes this
preimage regular. Inflation compatibility gives its value `y`.
This proves `regularIdeleClassInvariant_surjective_of_auxiliary`.

Finally assume `Finite (relativeIdeleClassCohomology F E 2)` and
`Nat.card (relativeIdeleClassCohomology F E 2) ≤ n`. The denominator
subgroup has cardinality `n`, so the surjective regular invariant forces
the regular subgroup to be all of cohomology. This is
`regularIdeleClassSubgroup_eq_top_of_auxiliary`.
`ideleClassInvariantEquivOfAuxiliary` applies the existing finite
invariant descent lemma to the inclusion of the regular subgroup and
its denominator-valued invariant. It yields an additive equivalence on
the whole actual cohomology group; the final theorem verifies its value
on every regular class.

The implementation follows the cited auxiliary-field argument, using
all denominator values directly instead of choosing only the value
`1/n` and then taking its multiples. The cohomological exactness,
regularity functoriality, degree annihilation, and finite-cardinality
arguments are imported supporting results. No new arithmetic axiom or
surjectivity assumption on the general idele-to-idele-class map is used.
