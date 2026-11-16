# Actual descent datum from corrected pinned atlas transitions

This internal construction takes an affine pinned atlas of an actual group
scheme and a supplied natural `RelativePinnedComparison`. The group on the
atlas scheme is the actual pullback of the original group. The construction
produces a `Descent.Datum` on this group over the atlas covering morphism.

`actualTransition` changes the endpoints of the assembled direct-pullback
transition to the actual pullbacks of the group on the atlas, using the
direct/iterated pullback comparisons. Their associativity coherence and the
assembled transition's naturality prove `actualTransition_pull`.
Cancellation of the intermediate endpoint comparison and the assembled
transition's cocycle prove `actualTransition_trans`.

`overlap` specializes this actual transition to the two projections of the
atlas double overlap. Its further pullbacks give the corresponding actual
transitions. On the triple overlap, the three atlas coordinates have the same
map to the original base. Therefore their actual transition composition law
is exactly the `Descent.Cocycle` equation. The pair consisting of this
overlap isomorphism and this equation is `datum`.

All content is derived internally from actual scheme pullbacks, the
previously assembled transitions and their proved laws. The natural pinning
correction remains an explicit input; the module does not establish its
existence, effectivity of the datum, invariant subgroup descent, or the
unconditional quasi-split inner-form theorem.
