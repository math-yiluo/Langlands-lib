# Relative openness for integer-valued root filtrations

This internal supporting construction adapts the published proof of
`ValuationBuildingData.eventually_val_eq` to explicit integer-valued building data.
It uses the existing root filtration without changing its definition.

The field `k` has a topology, continuous ring operations and open units. The group
scheme `G` is affine, and `B : IntegerValuationBuildingData v G` supplies the
building data for an explicit valuation with values in
`WithZero (Multiplicative ℤ)`. Rational points of `G` and of the supplied
centralizer carry `rationalPointTopology`; each root group carries the induced
subtype topology. No local compactness or completeness is assumed.

`eventually_val_eq` assumes the actual centralizer character valuation kernel is
open. For a nonidentity `u` in a relative root group, it proves that every
sufficiently near point `w` in that root group, other than the identity, has the
same root value as `u` at every apartment point.

The proof uses `Dynamic.opposite_cell_mem_nhds_one` to obtain a factorization
whose centralizer coordinate is small. The centralizer inclusion induces its
rational-point topology, so that coordinate belongs to the open character
kernel. Opposite-factor uniqueness identifies it with the quotient of the two
reflection elements. `IntegerValuation.IsOmegaCompatible.smul_eq_self` makes
this quotient fix the apartment. The published formulas
`normalizerAffineEquiv_reflectionElement` and `rootForm_reflectionCoroot`
then identify the two reflection functionals and hence the root values. The
root-group memberships use `IsOppositeFactorPair.inv_conj_mem` and
`reflectionElement_inv_mul_mem_centralizer`.

`isOpen_filtration` additionally assumes that some unit has nonzero integer
order. `exists_rootValue_sub_mul` supplies root elements with values
`s - nδ` for all integers `n`, with `δ ≠ 0`. Choosing the appropriate sign of
`n` gives a nonidentity element at any prescribed real depth. Local constancy
gives a neighborhood of that element contained in the filtration, including
the identity if it occurs. A subgroup containing a neighborhood of one of
its elements is open.

`filtrationOpenSubgroup` bundles this conclusion as an open subgroup of the
actual root group. Its underlying subgroup is exactly
`(B.filtration x α r).subgroupOf (B.rootGroup α)` for the supplied point, root
and real depth. The depth need not be nonnegative.

The provenance is internal: these are consequences of the cited published
Library results and the supplied building axioms. They do not construct
building data or assert existence of an apartment lift.
