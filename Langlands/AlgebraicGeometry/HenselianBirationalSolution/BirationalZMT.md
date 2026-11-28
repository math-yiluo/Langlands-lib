# The open immersion consequence of Zariski's Main Theorem

`isOpenImmersion_of_birational` applies to a separated, quasi-finite morphism
of finite type whose source is reduced and whose target is locally Noetherian
with integrally closed domain stalks. Its restriction to a dense open of the
source is assumed to be an open immersion. This is the form of BLR,
*Néron Models*, §2.3 Theorem 2′, p. 46, used for the graph projections.

The proof takes irreducible open neighbourhoods in the target. Over an integral
target, the given open immersion has irreducible dense source in the restricted
source, so reducedness makes that source integral when nonempty. The immersion
on the dense open identifies the generic stalks. Mathlib's factorization through
relative normalization gives an open immersion into the normalization. On affine
opens the normalization equals the target by integrally closedness and the
generic stalk isomorphism. Target locality finishes the proof.
