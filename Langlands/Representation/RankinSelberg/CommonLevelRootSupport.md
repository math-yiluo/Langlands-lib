# Uniform simple-root bounds from a common right level

This internal derived module constructs the actual elementary adjacent upper-unipotent
matrix `simpleRootUnipotent` and proves `root_bound`. It formalizes the common-level
support mechanism used in JPSS (1983), Section 4.5, printed pages 408–409, for an
arbitrary family of standard-character equivariant functions with one open right
level. It assumes no representation realization, support bound or parameter regularity.

The elementary matrix, its continuity, character value and diagonal conjugation
identity follow the algebra already implemented in the published
`Whittaker.SmoothSimpleRootSupportProof`. Those helpers there are private; this
module gives the reusable actual matrix and proves the same elementary identities.

The new uniformity argument uses compactness of the actual integral subgroup.
For each simple root, the continuous map `(t,k) ↦ k⁻¹ u_i(t) k` takes every `(0,k)`
to the identity. Openness of the given level and compactness give one neighborhood
of zero working for all integral `k`. Intersecting over finitely many roots and
refining to an actual valuation lattice gives `exists_uniform_lattice`.

At any nonzero family value on `diag(a) k`, right invariance and left Whittaker
covariance imply that the additive character is trivial on the lattice scaled by
`a_i/a_(i+1)`. The published additive-conductor characterization then bounds its
normalized absolute value by `q^(conductor − lattice_level)`. This bound works
for every family parameter and every integral factor. It also includes rank one,
where there are no simple roots. Neither compactness of the level nor analyticity
is used in this helper.

Source: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions* (1983), registered as `jpss-1983-rankin-selberg`.
The general common-level formulation is derived internal content, not a quotation
or a separately asserted theorem of the source. The module proves no integral
formula or factor specialization.
