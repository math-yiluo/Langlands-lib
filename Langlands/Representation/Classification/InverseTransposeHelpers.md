# Shared inverse-transpose constructions for normalized products

This module houses four existing helpers from Worker 1023's
`IrreducibleTwoFactorProductSwapProof`, also used by `SpehHermitian`.
Their types and defining terms are unchanged; the formerly private names
are exposed under the `hermitian` names used by the latter module.

- `hermitianItPullback` keeps the original smooth carrier and pulls its action
  back along inverse transpose.
- `hermitianGelfandKazhdanEquiv` applies the published Gelfand–Kazhdan theorem
  under the supplied topology at every positive rank.
- `hermitianItPullbackProductIso` uses the published inverse-transpose
  comparison to reverse normalized-induction blocks.
- `hermitianProductFunctor_obj_congr` transports normalized products across
  equality of block shapes and heterogeneous equality of their families.

These are shared implementation results. Moving them introduces no new
mathematical assertion and does not prove the remaining Speh unitarizability
statement. The two consuming companions retain their original source
correspondences and authorship.
