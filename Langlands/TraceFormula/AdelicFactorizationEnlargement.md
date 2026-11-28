# Enlarging the set of places in an adelic factorization

`IsAdelicFactorization.of_subset` enlarges the indexing set \(S\) of an
`IsAdelicFactorization` to a finite superset \(T\). The local functions at
places in \(S\) stay the same. At every place in \(T\setminus S\), the new
local function is the indicator of the tail subgroup at that place.

For an adelic point satisfying the old tail condition, the new tail condition
holds and every added factor is one. When the old condition fails but the new
one holds, some coordinate in \(T\setminus S\) fails subgroup membership.
Its indicator contributes zero to the finite product. If both tail conditions
fail, both indicators in the factorization formula are zero.

This follows from the restricted tensor product formula in
[`GeneralLinearBaseChangeLocal`](GeneralLinearBaseChangeLocal.md).
It lets two tests be expressed over the union of their finite sets of places,
as needed to apply the same scalar in
[`GeneralLinearBaseChangeGlobalMatchingStatement`](GeneralLinearBaseChangeGlobalMatchingStatement.md).
