# Reduction of rational generation to semisimple normal complements

Authors: Worker 1636 and Worker 1371.

The construction `almostSimpleRationalWord_of_normalIsogenyComplement`
takes an explicit proof of `SemisimpleNormalIsogenyComplementStatement`,
a simply connected group `G` over any field, and a rational point `g`.
It returns a finite list of rational points whose product is `g`, with
each entry belonging to the rational-point image of some closed normal
almost-simple subgroup scheme. The type `almostSimpleRationalGenerators G`
is the set of points satisfying precisely this existential image condition.
The list is chosen classically; its factors need not be distinct.

The supporting theorem
`simplyConnectedAlmostSimpleRationalGeneration_of_normalIsogenyComplement`
implements strong induction on the actual Lie dimension
of a smooth connected affine group. It retains the explicit
`SemisimpleNormalIsogenyComplementStatement` premise. Noncommutativity of a nontrivial
semisimple group over an arbitrary field is supplied by the proved helper
`IsSemisimple.noncommutative_of_nontrivial` of Worker 1371.
Neither construction nor supporting theorem proves the unconditional
rational-generation target.

For a simply connected group `G` and a subgroup `L` containing the
rational-point images of every closed normal almost-simple subgroup, the
induction first handles trivial `G` and almost-simple `G`. In the latter
case the identity inclusion supplies all rational points to `L`.

Otherwise, the failure of the defining almost-simple normal-subgroup
condition provides a proper nontrivial smooth connected closed normal
`H`. The structural premise gives a semisimple commuting complement `K`
and central-isogeny multiplication from `H ⊗ K` to `G`. Simple
connectedness makes this multiplication an isomorphism. The direct-factor
helpers of Worker 1371 make both factors simply connected.

Both closed factors have smaller Lie dimension. This follows for `H`
from its properness. If `K` were the entire group, injectivity of
multiplication would force `H` to be trivial, so `K` is proper as well.
The induction hypothesis applies to the inverse images of `L` in the
two rational-point groups. The commuting-product normality lemmas make
each internal almost-simple normal subgroup normal in `G`, allowing the
original containment assumption to supply these induction hypotheses.
Thus both full factor images lie in `L`, and multiplication of the
factors gives `L = ⊤`.

To construct the finite word, take the submonoid closure of
`almostSimpleRationalGenerators G`. This set of generators is stable under
inverse because each factor image is a subgroup. Induction on submonoid
closure therefore makes the closure a subgroup. The preceding conditional
generation theorem makes that subgroup the whole rational-point group.
Mathlib's `Submonoid.exists_list_of_mem_closure` then provides a finite
list and its product equality, and classical choice returns the list
together with both guarantees.

This proof is an internal reduction using the published definitions of
almost-simple and simply connected groups, Lie dimension induction,
and the explicitly assumed complement statement. Its mathematical route
does not assert the existence premise itself.
