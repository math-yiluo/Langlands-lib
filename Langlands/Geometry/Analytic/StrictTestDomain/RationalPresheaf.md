# Actual algebra presheaves on rational presentations

Author: Worker 36.

Fix a complete ultrametric normed field K and a presented strict affinoid
algebra P. The base category is the existing category `RationalData K P`
of chosen unit-radius rational presentations, with inclusions of their
actual multiplicative-seminorm loci as arrows. A presentation d already
has its constructed closed-ideal Tate quotient `d.algebra`, bounded map
`d.baseMap` from P, and a proved representation property against presented
strict affinoid tests. An inclusion h : d → e already induces the actual
bounded restriction `h.restriction : e.algebra → d.algebra`.

This module packages these constructed algebras and maps into presheaves.
It proves the functor laws, naturality of the structural and base-change
maps, and identification of the value at the whole-spectrum presentation.
It does not prove a sheaf or gluing property.

`PresentedStrictAffinoidAlgebra.toCommAlgCat K` sends a presented algebra
to `CommAlgCat.of K A` and a bounded map to its underlying K-algebra map,
wrapped with `CommAlgCat.ofHom`. The actual quotient carrier and its ring
and scalar operations are retained. The target category forgets the norm,
the bound and the choice of presentation. The identity and composition
laws are definitional. This functor does not require completeness of K.

`rationalBoundedPresheaf K P` is a functor from the opposite rational
inclusion category to `PresentedStrictAffinoidAlgebra K`. At the opposite
of d it has value `d.algebra`; at an opposite inclusion it has value the
bounded restriction for that inclusion. The previously proved
`Inclusion.restriction_id` and `Inclusion.restriction_comp` establish its
functor laws, with the order reversed by the opposite category.
`rationalBanachPresheaf` composes it with the existing `toBanachRing`,
retaining the actual complete normed rings and bounded ring maps.
`rationalPresheaf` composes it with `toCommAlgCat`, giving the
commutative K-algebra-valued presheaf used by later sheaf statements.
These are three views of the same quotient-algebra assignment.

`rationalBaseMap K P` is a natural transformation from the constant
presheaf with value P to the bounded presheaf. Its component at d is
`d.baseMap`. For an inclusion h : d → e, naturality is the existing
equality

    restriction(h) ∘ baseMap(e) = baseMap(d).

The proof uses `restriction_comp_baseMap`, reversing the equality to match
Mathlib's natural-transformation convention. It assumes no compatibility
map supplied by the caller.

Let Q be another presented strict affinoid algebra and φ : P → Q a bounded
K-algebra map. Write F for the published rational `pullbackFunctor φ`.
`rationalBoundedComparison φ` is the natural transformation

    rationalBoundedPresheaf K P
      → F.op ⋙ rationalBoundedPresheaf K Q.

Its component at d is the actual bounded comparison from `d.algebra` to
`(d.pullback φ).algebra` constructed by the published rational pullback
proof. The naturality square is exactly the bounded equality
`Inclusion.restriction_pullback_comp_comparison` from `RationalBaseChange`.
`rationalPresheafComparison` gives the corresponding natural transformation
of commutative K-algebra-valued presheaves; its naturality is obtained by
applying `BoundedAlgHom.toAlgHom` to that equality and using
`CommAlgCat.hom_ext`. `rationalPresheafComparison_baseMap` evaluates the
published comparison/base-map identity on an arbitrary a in P:

    comparison(d)(baseMap(d)(a)) = baseMap(F(d))(φ(a)).

Thus these transformations have the direction appropriate for pulling
algebra sections back along the spectrum map M(Q) → M(P). No assertion
that either comparison is an isomorphism is made.

The chosen object `whole K P` has denominator one and an empty numerator
tuple. Its locus is the entire spectrum. `existsUnique_wholeEvaluation`
applies its proved strict-test representation property to the identity
bounded map P → P. The required image containment follows from
`locus_whole`. This constructs a unique bounded map from the whole-object
quotient to P whose composite with its base map is the identity.
`wholeEvaluation` chooses this map, and `wholeEvaluation_comp_baseMap`
records that equality. For the opposite composite,
`wholeBaseMap_comp_evaluation` applies the published rational `hom_ext`:
precomposition with the base map reduces it to the preceding equality,
using associativity and identity of bounded maps.

`rationalBoundedWholeIso K P` uses the whole object's base map and this
evaluation map to give an isomorphism from P to the bounded presheaf's
value at the whole object. `rationalWholeIso` applies `toCommAlgCat.mapIso`
to obtain the corresponding commutative K-algebra isomorphism.
`restriction_whole_baseMap` proves that restriction from this whole-object
value to any d agrees with `d.baseMap` after the isomorphism. This is the
existing equation for the actual inclusion `toWhole d`. These results
identify a specific presheaf value; they do not depend on a sheaf theorem
or identify distinct quotient presentations by definitional equality.

The rational presheaves use the coefficient universe for carriers.
Completeness of K is used by the published representation and restriction
constructions. Empty numerator tuples, empty loci, zero or nonreduced
quotients, and trivial scalar valuations remain allowed. The algebra
category permits zero algebras. No nontriviality, injectivity of a base map,
surjectivity of a spectrum map or nonempty-cover assumption is introduced.
Radii remain one and the representation theorem used here tests presented
strict affinoids only. There is no assertion of finite-cover descent,
Tate acyclicity, the full analytic G-topology, a locally ringed space,
atlas gluing or an etale site. The module imports the published
`RationalBaseChange`; it does not need the separate continuity construction.

This is a derived construction from Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009). Definition 2.1.11 on printed/PDF p. 8
fixes the opposite bounded-algebra direction. Definition 2.2.1 and
Exercise 2.2.2(ii) on p. 9 give the domain universal property and rational
quotient context. Exercise 3.2.5(ii)–(iii) on p. 15 identifies affinoid
functions with the affinoid algebra and describes the structural sheaf
on the full analytic G-topology. The registered original is
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The present module implements the algebra and restriction assignment on
chosen unit-radius rational presentations and its derived functoriality;
it does not formalize the source's full structural-sheaf conclusion.
Fact 2.2.6(i), Tate acyclicity, on p. 10 is a further substantial descent
result and is not used or assumed here. The categorical packaging and
whole-value isomorphisms are derived from the already proved actual
quotient representation property, not quoted as separately named source
results.
