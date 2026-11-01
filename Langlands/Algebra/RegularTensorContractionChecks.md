# Regular-tensor comparison interface checks

Internal checks for `RegularTensorContractionStatements`, with the same source
and generalization boundary documented in that module's Markdown. These check
the full unapplied types and exact proposition contents at independent ring and
module universes. Unequal assignments `(uA,uM,uN) = (0,1,0)` and `(1,0,1)` are
checked explicitly. The comparison itself is not proved by these examples.

`CompetingStructures` installs different ring, group and module instances and
different group and action instances on both actual tensor carriers. It first
checks that these competitors really are active. Explicit original arguments
then recover the published quotient and group, residual action, universal
contraction, both types of comparison maps, comparison content and whole-map
naturality with the actual restriction to nondegenerate parts. The equations
are definitional equalities.

`ZeroIntegerAction` uses the zero original action of `ℤ` on the nonzero group
`ℤ` while retaining the right regular first tensor factor. It checks that the
original ambient action is degenerate and the whole contraction is zero.
Balancing with the regular first factor gives `a ⊗ m = 1 ⊗ 0 = 0`, so this
regular-source tensor is a subsingleton. The actual nondegenerate part is the
zero additive subgroup. The unfolding of `ModuleComparison` retains the
nondegeneracy guard on any identification with the whole ambient group.
The boundary checks never assert such an identification for this zero action.

`RegularIntegerAction` uses ordinary left multiplication, proves its original
nondegeneracy with the fixing idempotent `1`, checks the contraction's pure
value by the published universal lift, and detects a nonzero pure tensor by
that contraction. Both integer examples use no theorem proving the main
comparison. The final zero-ring check permits `PUnit` at any ring universe
and an arbitrary ambient additive group at an independent universe.

All checks are intrinsic constructions and scope tests derived from the
published interfaces; their literature provenance and arbitrary-ring
generalization are explained in the statement module's Markdown.
