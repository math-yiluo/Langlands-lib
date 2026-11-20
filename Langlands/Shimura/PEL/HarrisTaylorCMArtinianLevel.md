# Pointed Harris levels over local Artinian thickenings

`SpecArtinianMonodromySurjectivityStatement` concerns the actual fundamental
groups of finite étale covers evaluated at a geometric point of the smaller
spectrum and its composite with the immersion. Its proof,
`specArtinianMonodromySurjectivity`, applies to every surjection of local
Artinian rings.

The spectrum of a local Artinian ring has one point, so the induced closed
immersion is surjective. Its pullback to a finite étale cover is again a
surjective closed immersion and induces a homeomorphism. For a finite étale
cover, categorical connectedness agrees with connectedness of the total
space. A clopen subset gives a subcover, and a monomorphism of finite étale
covers is both an open and a closed immersion. The pullback of each Galois
object therefore has connected total space and is connected in the Galois
category. Its geometric fibre carries a transitive action of the smaller
spectrum's fundamental group. The pointed pullback fibre equivalence
intertwines this action with the action through the fundamental-group map on
the original fibre. Mathlib's surjectivity criterion for actions on the fibres
of Galois objects gives the result.

`framedPositiveActionTowerBaseChange_surjective` applies this surjectivity
condition to the actual pointed Harris tower. The compatible-frame equivalence
preserves the right similitude actions and intertwines the monodromy actions.
The image of a fixed right orbit under the induced orbit equivalence is fixed
by the entire target monodromy group, since each of its elements has a
preimage. This gives a preimage for the existing level pullback at every
Harris level. A compatible source frame supplies the faithfulness proof in
the construction of the changed polarized action.

These results are derived from the Library's geometric fibre functor, pointed
pullback comparisons and compatible-frame action, together with Mathlib's
Galois category criterion. The tower theorem transports levels for a given
polarized action and its given pulled-back dual evaluation data.
