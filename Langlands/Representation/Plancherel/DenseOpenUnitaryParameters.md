# Ambient and unitary dense open parameter regions

`IsDenseOpenUnitaryRegion` records that a set of unramified characters is
open and dense, and that its inverse image in the unitary characters is
dense. `IsDenseOpenUnitaryRegion.inter` and `isDenseOpenUnitaryRegion_biInter`
show that finite intersections keep these properties, because the sets and
their unitary inverse images are open. `isDenseOpenUnitaryRegion_nonzero`
shows that the nonvanishing locus of a nonzero regular function is such a
region, using `rationalUnramifiedRegular_dense_nonzero` and
`ActualCommonLeviV3.dense_rationalUnitaryRegularRestriction_ne_zero`.

These regions express the density of the regular unitary points used in the
proof of Corollary V.2.3 of Waldspurger, printed p. 294 (source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`), where the
estimate on the dense set `U` of regular points is extended by continuity.
