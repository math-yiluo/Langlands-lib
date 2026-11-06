# Hom bounds for natural gluing

This is derived algebraic support for the endomorphism argument associated with
Renard, *Représentations des groupes réductifs p-adiques* (9 July 2026),
VI.5.3, printed p.173 / PDF p.179. It uses the existing actual functor filtration,
its published objectwise evaluation, and the restriction and quotient descent
bounds in `HomBounds`. It does not prove Frobenius reciprocity, the geometric
lemma, the distinguished geometric piece comparison, or the maximal-Levi
endomorphism dichotomy.

The coefficient field, acting monoids, representation carriers, and source
category have independent universes. No irreducibility, smoothness, admissibility,
or finite dimensionality is assumed in this module. All lengths are the
extended-natural module lengths over the coefficient field of the full spaces
of intertwining maps.

`equivLeftOfIso` transports the source of an intertwining map along an
isomorphism of actual `Rep` objects. It applies `equivLeft` to the representation
equivalence induced by that isomorphism; its forward map precomposes with the
inverse source isomorphism.

`length_le_sum_of_isGluedFrom` evaluates the supplied natural filtration at an
object and applies the actual graded-quotient Hom length bound. The supplied
natural graded isomorphisms identify the evaluated graded Hom spaces with the
specified pieces. Reindexing the finite sum removes the permutation allowed
by unordered gluing. Every supplied occurrence contributes separately, including
repeated or zero pieces. The statement also permits an empty list.

`length_le_of_single_piece_of_isGluedFrom` assumes that the Hom lengths from
every piece other than a specified occurrence vanish. The finite sum then
reduces to that occurrence, which bounds the whole Hom space.

`exists_scalar_of_length_end_le_one` proves scalarity for every endomorphism
when the endomorphism space has length at most one. If the identity intertwiner
is nonzero, the length-one proportionality lemma applies to it. If the identity
is zero, every carrier vector and every endomorphism are zero, and scalar zero
suffices. The latter case requires no nontriviality assumption.

`scalar_or_exists_off_piece_of_isGluedFrom` additionally takes an actual linear
equivalence from the endomorphism space of any representation to the Hom space
out of the glued value. It also assumes a specified piece has Hom length at most
one. For each endomorphism, it concludes that the endomorphism is a scalar
multiple of the identity or that some other piece admits an actual nonzero
intertwiner to the target. The proof splits on the existence of such a map.
When no such map exists, each other Hom space is a subsingleton, its length is
zero, and the preceding bounds give endomorphism length at most one.

The equivalence, the gluing, and the distinguished-piece bound are explicit
premises. Applying this support to the maximal-Levi theorem still requires
constructing them from the actual adjunction and geometric lemma and identifying
the remaining geometric pieces.
