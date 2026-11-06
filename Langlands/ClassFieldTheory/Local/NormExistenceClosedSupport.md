# Closedness of actual local norm subgroups

For any finite extension of p-adic fields, in independent arbitrary universes,
the actual determinant-norm subgroup is closed for the supplied topology.
`ClosedLocalNormSubgroups` is the Prop-valued assertion of this result, and
`closedLocalNormSubgroups` proves it. No Galois assumption is needed.

The integral-unit subgroup is open: it is the inverse image of the nonzero
valuation sphere of radius one under the continuous map from field units to
the field. Its elements are exactly the units of normalized order zero.
The proved relative norm-order criterion then identifies the intersection of
the norm group with the integral units below with the norm image of the
integral units above. The latter image is compact and hence closed.

A general topological-group lemma finishes the argument. If a subgroup's
intersection with an open subgroup is closed, the same intersection with its
topological closure is contained in the subgroup. Every point of the closure
can be translated into that open subgroup by an element of the original
subgroup, so the point itself belongs to the original subgroup.

This is derived internal support. It uses the published compact integral-unit
filtration, the actual determinant norm and its continuity, the norm-order
criterion, and Mathlib's valuation topology. It asserts neither norm-subgroup
existence nor a reciprocity map.
