# Smoothness in a closed linear submodule

`Langlands.Analysis.ClosedSubmoduleSmoothnessStatement` says that a function
from an open subset of a real normed space into a closed linear submodule of
another real normed space is smooth if and only if its ambient-valued function
is smooth. The Lean statement takes the two normed spaces in a common universe.

If the ambient function has a derivative at a point, its derivative in any
direction is a limit of difference quotients in the submodule. Closedness
places the derivative in the submodule. The ambient and submodule norms on
the derivative remainder agree, so the restricted operator is the derivative
of the submodule-valued function.

The continuous linear operators with image in the submodule form a closed
submodule, by continuity of evaluation at each direction. The proof lifts the
derivative family to this closed submodule by induction on differentiability
order. The linear map sending each operator to its submodule-valued form is
bounded by the operator norm. Composing with it gives the required derivative
family. The converse is composition with the continuous linear inclusion.

This is an internal calculus lemma for differentiating the compact profile
action of a real standard module in its Banach completion.
