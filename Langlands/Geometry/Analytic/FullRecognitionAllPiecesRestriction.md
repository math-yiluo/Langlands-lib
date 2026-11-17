# Shrinking and combining properties over all recognized pieces

This internal module develops consequences of the published
`HasAllPiecesAt`, `IsFiniteOver.exists_small`, and clopen restriction API.
It uses independent field, space, and index universes, with no global
Hausdorff, nontrivial valuation, or strictness assumption.

`allPieces_restrict` transfers the property on the pieces of a finite
neighborhood `V₀ → U₀` to supplied pieces of a smaller open source `V` and
smaller target `U`. It assumes `V ⊆ V₀` and `U ⊆ U₀`. The pointwise
property must survive postcomposition with a flat surjective bounded map
when the old map is of finite type. For a target piece `W`, the old
finite-neighborhood hypothesis constructs `P₀`. The locus equality for
the supplied new piece `P` identifies it with `P₀ ∩ V`. Since `V` is
open, this is a clopen part of the affinoid spectrum of `P₀`. The
published clopen restriction theorem gives flatness and surjectivity.
The actual pair-system restriction identity factors the new map through
this restriction, so the assumed stability applies at the original point.

`HasAllPiecesAt.exists_small` uses finite-neighborhood shrinking and the
preceding transfer lemma to preserve the property inside any prescribed
neighborhood of the point. `HasAllPiecesAt.and` shrinks the first source
into the second, intersects the targets, and restricts the source to the
preimage of this intersection. It transfers both certificates to these
same neighborhoods. `HasAllPiecesAt.mono` applies a pointwise implication
to an unchanged certificate.

`hasAllPiecesAt_isEtaleAtPoint_iff` identifies a joint
`IsEtaleAtPoint` all-pieces witness with separate all-pieces flat and
unramified witnesses. The forward implication projects the conjunction.
For the reverse implication, flatness survives a flat source
restriction by composition. A surjective restriction is formally
unramified and finite, hence of finite type, so the published pointwise
unramified composition law applies as well. The conjunction lemma then
constructs a single certificate.

`AllPiecesJointEtaleStatement` quantifies that equivalence over the two
presentations, actual strong map, and point; `allPiecesJointEtale` proves
it. These are internal deductions, with no additional external source
assertion. They do not construct finite neighborhoods for a map whose
finiteness is unknown, extend finite families to all pieces, or prove
étale right cancellation.
