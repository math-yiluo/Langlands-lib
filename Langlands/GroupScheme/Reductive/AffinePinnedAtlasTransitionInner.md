# Actual adjoint points inducing corrected atlas transitions

For an affine pinned atlas of a group scheme over an arbitrary scheme, a
supplied natural pinned comparison, and a supplied full-centre fppf quotient
with its compatible conjugation action, this construction chooses an actual
relative quotient point inducing each inverse corrected atlas transition.
Its specification is equality of actual group-scheme automorphisms over the
test scheme.

The proof first pulls back the quotient and action to a common chart test.
The full centre commutes with base change, and the pulled-back action still
restricts to conjugation. The chart innerness theorem gives a base point of
the pulled-back quotient. The pullback point equivalence gives the required
relative point of the original quotient, with the same evaluated action.

The inverse images of target atlas components form a small disjoint
decomposition. The point assembly construction glues the chart witnesses
on those components to a witness for each chart-to-atlas transition.
Repeating this construction over the source components gives a point for
the full atlas transition. Direct pullback respects inverse isomorphisms,
so the restrictions have the orientation required at both stages. Classical
choice selects the point from this existence theorem; the specification
retains its exact evaluated automorphism.

The provenance is internal composition of chart transition innerness,
base-change compatibility for full-centre quotients and actions, and actual
point assembly on arbitrary disjoint components. No finiteness or affine
hypothesis is imposed on the test scheme. Existence of the supplied natural
pinned comparison remains a separate prerequisite.
