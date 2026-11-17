# Flat quasi-compact separated schemes as a Cartesian category

This internal auxiliary construction supports canonical affinization over a PID.
It does not impose a PID hypothesis: flat, quasi-compact, separated morphisms over
any scheme are stable under fibre products and contain the identity morphism.

`flatQcSeparated S` is this property on `Over S`, and `SchemeCategory S` is its
full subcategory. Its Cartesian monoidal structure uses the actual fibre product
and identity over the base, with the inherited projections. The proof of the
product universal property lifts the universal morphism through the full
inclusion. `inclusion S` is the resulting fully faithful monoidal functor.

`restrictedGroup G` lifts an actual group scheme satisfying the three geometric
hypotheses through this full inclusion, using Mathlib's fully faithful transport
of group objects. `restrictedGroupIso G` identifies the forgotten group with
`G`; its underlying scheme morphism is the identity. The unit and multiplication
compatibilities reduce to identity compositions. No finite-type, affine, smooth, connected or commutative
hypothesis occurs. This is an internal categorical organization of the existing
scheme and group-object APIs, rather than a separate assertion from literature.
