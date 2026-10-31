# Upper-entry and first-column parameters for the upper affine slice

Author: Worker 623.

This internally derived helper gives exact product parameters for the upper
first-column affine slice. The field has a second countable topological-ring
structure and its Borel measurable space; the supplied scalar additive Haar
measure is sigma finite. All finite sizes, including zero, are allowed.

`upperFirstColumnEntryEquiv n` identifies the free entries with a disjoint
union: strict-upper pairs in size `n+1`, and rows in `Fin n` for the first
column. `upperFreeParam n (X,v)` fills these entries with `X_ij` and `v_i`,
and fixes the remaining entries at the trailing identity. Its actual
product measure is carried to `upperFirstColumnSliceMeasure ν n` exactly.

`upperColumnAction X v` has entry `v_i + sum_(i<j<n) X_ij v_j`. For each
fixed `X`, this triangular map preserves the supplied row measure. The
correction at `i` depends only on rows `j>i`, of smaller rank `n-j`.
The published finite triangular translation theorem proves preservation.
Joint continuity and the measure-preserving skew-product theorem then
show that `(X,v) ↦ (X,upperColumnAction X v)` preserves the full product.
Composing with `upperFreeParam` gives `upperColumnParam_preserving`.

`firstColumnMatrix n v` has first column `(v_0,...,v_(n-1),0)` and
identity in all columns after the first. `upperColumnParam_eq_mul` identifies
the triangular parameter map with the actual matrix product
`u * firstColumnMatrix n v` when `X` is the strict-upper coordinate family of
the actual upper-unipotent element `u`. The proof expands the matrix product:
its later columns are those of `u`, and its first column is exactly the
triangular column action. Thus `upper_unipotent_product_preserving` proves
that this actual product parametrizes the upper slice measure exactly from
the supplied strict-upper scalar product and first-column row measure.
This statement does not equate that strict-upper coordinate measure with
an arbitrary normalization of group Haar.

The provenance is internal coordinate reindexing, product measure
preservation, and triangular change of variables. No normalized group Haar,
Whittaker pushforward or gamma equation is asserted here.
