# Finite representatives and coordinates for lattice faces

Author: Worker 836, Task 5326. Derived helpers for the Xi upper bound.

`exists_finite_representatives` applies finite-image representative selection
to finitely many integer-valued additive maps with values in a bounded box.
Every point with such values differs from one of the finite representatives by
a point in the common kernel.

`exists_basis_coord_bound` uses Smith normal form over the integers. Each basis
coordinate in the submodule, multiplied by a nonzero integer diagonal entry,
is the restriction of an ambient basis coordinate. The absolute value of the
diagonal entry is at least one, giving the asserted coordinate inequality.
These are derived linear algebra helpers using Mathlib's existing theorems.
