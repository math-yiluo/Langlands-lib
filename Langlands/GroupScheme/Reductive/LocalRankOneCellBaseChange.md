# Coordinate-preserving base change of actual rank-one cells

This internally derived prerequisite combines actual opposite-root
parametrizations, the standard additive and split-torus base-change
comparisons, and preservation of open immersions by pullback. It makes no
new external-source correspondence claim.

`LocalRankOneCell.isOpenImmersion_baseChange` starts with an actual open
negative-root, torus, positive-root cell over a commutative ring. After
arbitrary commutative algebra base change, the same cell in standard
coordinates remains an open immersion. The product comparison identifies
its map with the actual pullback of the original cell map. Pullback and
precomposition with an isomorphism preserve the open immersion.

`baseChangeCellData` packages this open cell and the base-changed root
parametrizations as ring cell data. The exponent of the root is unchanged.
Its two equivariance fields are the pointwise equivariance of the actual
base-changed root maps.

`baseChangePointsEquiv_cellPt` identifies the resulting three-factor point
under the actual pullback-point equivalence with the same root coordinates
over the original base and the transported actual torus point. Its proof
uses the multiplicativity of that equivalence and its existing root-point
and torus-point identities.

No locality, reducedness, noetherianity or field assumption is required.
The original root parametrizations and open immersion remain supplied inputs.
