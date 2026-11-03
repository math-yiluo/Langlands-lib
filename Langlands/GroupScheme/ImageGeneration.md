# Closed subgroup envelopes of actual scheme morphisms

This is internal universal-property infrastructure for the source construction
in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
the paragraph preceding Proposition 3.3.5, printed p.109 (PDF p.135);
registered source `conrad-gabber-prasad-2015-pseudo-reductive`.
It does not prove that the envelope is representable.

For an arbitrary base scheme `B`, an actual group scheme `G`, and a morphism
`f : V ⟶ G.X` of schemes over `B`, `closedImageEnvelope f` is the intersection,
on every test scheme, of the ranges of all actual closed subgroup inclusions
through which `f` factors. Its subgroup and restriction laws follow from the
corresponding laws for each range. The intersection ranges over actual group
schemes and actual morphism factorizations, including competitors that are
neither smooth nor reduced.

`SubgroupFunctor.ContainsImage` quantifies over all test schemes. The universal
point of `V` proves that this is equivalent to membership of `f` itself.
`FactorsThrough` records a scheme morphism and its inclusion equation, and is
equivalent to containment in the range functor. The envelope contains the image
and is contained in every competing represented closed subgroup functor.
This intersection need not be the abstract subgroup generated separately on
each test scheme; no such identification is claimed.

`GeneratedImage f` consists of an actual group scheme, its actual closed
inclusion, and representation of the envelope by that inclusion. It assumes
neither existence of such data nor smoothness of an image closure.
Given these data, `factor` is the unique actual morphism into the representative
whose composite is `f`. The equation is proved on every test scheme by
precomposition. `minimalHom` is the unique group-scheme homomorphism into any
other closed subgroup through which `f` factors, commuting with the inclusions.
It is constructed by the existing Yoneda lifting theorem for represented
subgroup functors. Closed immersions provide the monomorphisms used for
uniqueness. `iso` identifies any two representatives over `G`.

The definitions of the intersection and the representative package are an
internal formulation of the source's generated closed subgroup. The included
proofs establish only their intrinsic universal-property laws. Geometric
existence, smoothness, geometric connectedness, and positive finite-product
dominance require separate proposition targets and proofs.
