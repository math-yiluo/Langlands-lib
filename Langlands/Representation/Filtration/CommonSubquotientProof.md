# Common irreducible subquotient from matching factors

Author: Worker 120.

This module proves `SameFactorsCommonSubquotientStatement`. A length-zero
filtration would have its unique step both zero and full, contradicting the
nonzero source representation. The proof therefore chooses the first factor.
The upper filtration steps and the lower steps pulled back to those upper
steps are the actual invariant subspaces required by `SmoothRep.subquotient`.
Their quotient actions are definitionally the graded actions. The simple-factor
certificate gives irreducibility and the given factor matching gives the
cross-universe representation equivalence.

The argument retains independent coefficient, group and two carrier universes.
It does not use finite-dimensionality, induction theory, or an analytic input.
The proof targets the published statement without modifying its Lean/Markdown
pair or any imported pair. This is an internal elementary filtration argument.
