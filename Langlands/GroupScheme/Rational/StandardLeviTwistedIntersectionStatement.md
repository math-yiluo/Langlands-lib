# Twisted intersections of standard Levis

`StandardLeviTwistedIntersectionStatement` is an unproved structural target.
For every field, connected reductive group, maximal split torus and generic
cocharacter, it applies to every Coxeter system on the actual scheme relative
Weyl group `relativeWeylGroup i = N(k)/Z(k)` satisfying
`IsRelativeWeylCoxeterRealization i ν cs`. The labels are the actual simple
relative roots, computed from the full, possibly nonreduced root set.

Its conclusion is `IsStandardLeviTwistedIntersection i ν cs`. For all finite
label subsets `I,J`, all `w` minimum in `W_I w W_J`, and every scheme-normalizer
point `n` with quotient class `w`, this property states

`L_J ∩ Int(n)⁻¹(L_I) = L_(intersectionSubset cs I J w)`.

Here each `L` is the published `standardLevi` subgroup functor at the character
set `rootSet i ν` of its finite labels. The equality is of subgroup functors,
so holds on every test scheme, including nonreduced test schemes.
`intersectionSubset` is the subset of `J` whose simple reflections belong to
`w⁻¹ W_I w`. The preimage is `SubgroupFunctor.comap (G.innerIso n).hom`.
At rational points this is `n⁻¹ L_I(k) n`, with the source-side orientation used
by the actual geometric term and `actualLeviIntersection`.

The target quantifies every lift, rather than a chosen quotient section. It
makes no restriction on characteristic, perfectness, reducedness of the root
system, splitness or quasi-splitness of the group. Empty simple-root types and
empty or full subsets are included. Its only universe is the arbitrary field
and scheme universe `u`; there is no representation-carrier universe involved.

Two elementary adapters are proved. The first,
`standardLeviPoints_twistedIntersection_of_functor_eq`, evaluates a supplied
all-test equality at the identity test object and applies the published
`SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map`. It needs no
normalizer, maximality or connected-reductive hypotheses. The second,
`IsStandardLeviTwistedIntersection.rationalPoints`, specializes that adapter
to every lift covered by the property. Both use the literal published
`RationalPointFamily.levi` point subgroups; no replacement family or topology
is introduced.

The provenance is internal: this is the precise structural prerequisite for
the actual geometric-term reduction in the induction-compatibility proof.
Aubert 1995, the proof of Theorem 1.7(2) after (1.8), printed p.2182 / PDF p.4,
groups source-side intersections `L_J ∩ w⁻¹ L_I w = L_K` before applying Solomon
cancellation. That passage is at p-adic-group scope; the all-field, all-test
formulation here is an explicit strengthening requested of the structural
prerequisite, not a claim that Aubert states this scheme-theoretic version.
The existing standard-Levi intersection target concerns nested
Levi–parabolic intersections and does not state this twisted equality.

Neither adapter proves the structural target. Transport from the scheme
quotient to the actual normalizer of the torus-point image modulo its full
centralizer also requires the separate point-normalizer and point-centralizer
comparisons and Coxeter-index transport. Those obligations and the actual
normalized representation-theoretic term reduction remain open here.
No instance, axiom or proof of the target is supplied.

Source ID: `aubert-1995-duality`.
