# Representability from an fppf quotient presentation

Author: Worker 1150. The common-kernel formulation and intended geometric
applications were proposed by Worker 1001.

This internal helper concerns an arbitrary base scheme `S` and actual
presheaves with values in `Type (u + 1)`. It supplies the local-surjectivity
bridges and quotient identification below.

`generate_singleton_mem_fppfTopology` proves that a single actual scheme
morphism over `S` with surjective, flat, locally finitely presented underlying
morphism generates a covering sieve in the slice fppf topology. The proof
uses the equivalence between sieves on a slice object and on its underlying
scheme and Mathlib's singleton fppf precoverage lemma.

`isLocallySurjective_schemeYoneda_map` then proves local surjectivity of the
induced map on represented presheaves. For every test-scheme point, the
pullback of the singleton covering sieve lies in the image sieve: a
factorization through the scheme cover is precisely a lift of that point.

`isLocallySurjective_of_fppf_projections` treats an arbitrary representable
presheaf morphism `a : F ⟶ G`. It assumes that every represented pullback
projection is surjective, flat and locally finitely presented. For a section
of `G` over a test scheme `T`, lifted Yoneda gives a map from the represented
presheaf of `T`. The chosen representing pullback has an fppf projection to
`T`. Evaluating its commutative square at the identity gives a lift of the
restricted section, so the image sieve contains that covering projection.
`isLocallySurjective_of_isEtale_isSurjective` specializes this argument to
the published geometric etaleness and surjectivity predicates. These four
lemmas require neither presheaf to be a sheaf.

The quotient identification concerns an actual type-valued fppf sheaf `F`
and two presentations with domain the represented sheaf of a scheme `W`
over `S`. One presentation is a natural transformation `a` to `F`; the other
is induced by an actual scheme morphism `q : W ⟶ M`. The general hypotheses
require both transformations to be locally surjective for the fppf topology
and to identify precisely the same pairs of scheme-valued points over every
test scheme.

`exists_iso_of_locallySurjective_of_same_kernel` constructs an actual natural
isomorphism from the functor of points of `M` to `F`, with a factorization
of `a` through `q`. Local
surjectivity gives epimorphisms in the category of sheaves. Mathlib's regular
epimorphism theorem makes these effective epimorphisms. The sectionwise
kernel comparison implies compatibility on maps from every sheaf, by
evaluation at each test scheme and section. Effectiveness then gives
morphisms in both directions. Their factorizations and the epimorphism
cancellation laws show that they are inverse.

`representableBy_of_locallySurjective_of_same_kernel` converts the resulting
natural isomorphism to an actual `Functor.RepresentableBy` witness.
`representableBy_of_fppf_quotient` specializes the second local-surjectivity
hypothesis to a surjective, flat, locally finitely presented scheme quotient
`q`, using the represented-cover lemma above. Its first local-surjectivity
hypothesis can be supplied by either projection lemma when applicable.

These arguments construct no affine quotient and assume no field,
separation, or geometric condition beyond the displayed hypotheses.

These are internal derived consequences of the published algebraic-space
interfaces and Mathlib's sheaf theory. They do not assert a new original
literature theorem or prove the parent group-space representability target.
