# The field chart at a nonsplit finite CM place

The sum of the local degrees above a finite place is at most two.
If two upper places occur, both degrees are one. The completed tensor
comparison then identifies the actual quadratic center with a product of
copies of the base completion. Its conjugation is nontrivial because the
original CM field injects into an upper completion. A nontrivial
involution of the product interchanges its two primitive idempotents and
hence interchanges its factors. This gives the split center criterion.

At a nonsplit place, there is therefore exactly one upper place.
`nonsplitCompletionCenterEquiv` is the actual center evaluation at that
upper completion. The unique-place degree formula gives degree two.
`nonsplitCompletionCenterEquiv_conjugation` identifies the transported
involution with the unique extension of CM conjugation to the upper
completion by computing on pure tensors.
