# Locally constant compact sections

This module proves `LocallyConstantCompactSectionsStatement` from Renard (9 July
2026), II.2.4, Example, printed page 38 / PDF page 44, source
`renard-2026-representations-groupes-reductifs-padiques`.

The internal subgroup `LocallyConstantCompactSections.supported U` consists of
the existing pointwise test functions whose support is contained in `U`. The map
`extend` uses the published `RegularProjectorSheaf.extendTest`, which extends a
locally constant function by zero across the clopen complement of `U`; its support
is compact because it is contained in the compact closed set `U`.

Restriction to `U` is the inverse. The two inverse identities and additivity are
checked pointwise, separately inside and outside `U`. Thus `equiv` identifies
the actual sections of the locally constant scalar sheaf with this subgroup.
These helpers are derived constructions for the Example, not additional
literature assertions.

Subgroup monotonicity follows from containment of supports. Every test function
belongs to the subgroup indexed by its own support, which the published
pointwise-test results show to be compact and open. Restricting a function
supported in `U` from `V` to `U` and extending it again fixes it. Restriction
to `V ∖ U` is zero, since every point there is outside its support. These are
the exact clauses of the published statement, with its space universe retained.
