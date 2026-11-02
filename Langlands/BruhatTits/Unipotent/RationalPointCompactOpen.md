# Compact open subgroups of actual rational points

This internal construction is a prerequisite for compact-open containment in
actual dynamic unipotent radicals. It uses the existing group law on
`RationalPoint F G.X = (Over.mk (𝟙 (Spec F)) ⟶ G.X)` and installs exactly
`rationalPointTopology F G.X`. The identity-test comparison with `RingPoint`
is the multiplicative homeomorphism from
[RationalPointGroups](../../AlgebraicGeometry/PointTopology/RationalPointGroups.md):
precomposition preserves products.

For an affine group scheme of locally finite type over a topological ring,
the shared `PointTopology.rationalPoint_isTopologicalGroup` transfers the
published group continuity theorem.
It also transfers Hausdorffness from the value ring, and local compactness
from a locally compact Hausdorff topological value ring. Total disconnectedness
passes through the canonical homeomorphisms and the evaluation embedding into
the full function space on the coordinate ring.

For every `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]`
and `[IsNonarchimedeanLocalField F]`, the existing valuation topology is
Hausdorff and nonarchimedean, hence totally disconnected. The preceding
transfers show that actual rational points of a finite-type affine group
scheme are locally profinite. The published Van Dantzig theorem, applied to
the whole-group neighborhood, supplies a compact open subgroup.
`rationalPointCompactOpenSubgroup` selects one together with its compactness
proof. No smoothness, reductivity, splitness, or cocharacter hypothesis is
needed for this prerequisite. It preserves the arbitrary universe and both
local-field characteristics.

These are internal derived constructions from the Library's actual
point-topology comparisons, `AffineGroupProofs`, and `LocallyProfiniteProof`.
This module does not assert the dynamic radical is closed or prove its
contracting-family construction. Those are separate obligations in the parent
proof; this module supplies the ambient compact open subgroup without an
extra topology or compact-open-existence premise.
