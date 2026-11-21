# Groups of multiplicative type over normal bases are locally isotrivial

Workers 616 and 370.

`Langlands.GroupScheme.multiplicativeTypeNormalIsotrivial` proves
`Langlands.GroupScheme.MultiplicativeTypeNormalIsotrivialStatement.{u}`
in every universe. For a group of multiplicative type over a normal
scheme, it gives finite étale surjective splitting covers of open
neighbourhoods of all points. On an irreducible normal scheme it gives
a finite étale surjective splitting cover of the whole scheme.

The proof obtains normal-base isotriviality for finitely generated
abelian étale local systems by applying
`EtaleLocalSystem.etaleLocalSystemNormalIsotrivial_of` to
`finiteOrderCongruenceDetection`, `finiteLocallyConstantRepresentable`,
and `etaleLocalSystemIsotrivialSpreading`. These theorems supply
congruence detection for finite-order automorphisms, representability
of finite locally constant étale sheaves, and spreading of
isotriviality from a local ring to an open neighbourhood.

`multiplicativeTypeNormalIsotrivial_of_localSystem` applies that
local-system result to the group's actual relative character sheaf.
On each resulting cover, the Cartier base-change comparison identifies
the restricted character sheaf with the characters of the pulled-back
group. Constancy of those characters gives diagonalizability by
`relativeCharacterConstancy`.

This is the splitting assertion of Corollary B.3.6 in Brian Conrad's
*Reductive group schemes* (2014), pp. 293–295, registered as
`conrad-2014-reductive-group-schemes`. The character-sheaf reduction
comes from Proposition B.3.4 and the first paragraph of the proof of
Corollary B.3.6.
[Conrad, Corollary B.3.6](https://math.stanford.edu/~conrad/papers/luminysga3.pdf#page=293)
