# Equivariant retractions onto normal adjoint subgroups

Worker 1372.

This module defines a structural proposition target and proves nothing.
`NormalAdjointEquivariantRetractionStatement.{u}` concerns group schemes over
an algebraically closed field `k : Type u`, for arbitrary `u` and in arbitrary
characteristic. It assumes `IsAdjoint G` and `IsAdjoint H`, a closed inclusion
`j : H ⟶ G` with normal all-test range functor, a split torus `S`, and actual
automorphic actions `b` on `G` and `c` on `H` for which `j` is equivariant.

Here `IsAdjoint` is the published predicate: connected reductive with finite
scheme-theoretic centre and trivial centre functor. In particular both groups
are smooth, affine and connected. Their centres are the full scheme-theoretic
centres, including any infinitesimal points, and triviality is equality with
the bottom subgroup functor. Normality of `range j` is also tested on all
schemes over `Spec k`.

The conclusion supplies an actual group-scheme homomorphism `r : G ⟶ H` with
`j ≫ r = 𝟙 H`, equivariant for the two actions on every test scheme. It implies
surjectivity of `r` on every original test scheme by its section; the statement
asks for the retraction itself, rather than a field-point projection. Neither a
retraction nor a direct-product decomposition is assumed. No semigroup, weight
support, coordinate realization or comparison proposition is a premise.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), source ID `conrad-gabber-prasad-2015-pseudo-reductive`, in the proof of
Proposition 3.3.10(c), printed pp.113–114 / PDF pp.139–140, especially the
last normal-subgroup reduction on printed p.114: after passage to the maximal
adjoint quotients the normal subgroup is a direct factor. The field has already
been made algebraically closed in that proof. The present target isolates this
structural step with adjointness of both groups explicitly assumed. It does not
assert the preceding radical or centre reductions.

The packaging is derived, since the source does not state this exact equivariant
retraction proposition. For the normal adjoint subgroup `H`, its complementary
factor is the scheme-theoretic centralizer of `H` in `G`. Indeed, in a direct
product `H × K`, that centralizer is `Z(H) × K = K`, since the full centre of
`H` is trivial. Every automorphism of `G` preserving `H` preserves this
centralizer and hence the projection onto `H`. Applying this to the supplied
compatible action gives equivariance of the projection. This reasoning uses the
actual direct-product isomorphism and scheme-theoretic centralizer, so the
claimed identities hold after every base change and on all test schemes,
including nonreduced tests. Establishing the direct factor and implementing this
argument are obligations of the separate proof, not results of this module.

This structural target supports the normal-subgroup case of semigroup
intersection. It does not prove semigroup functoriality, realization, the radical
and adjoint-quotient reductions, or `SemigroupComparisonStatement`. In particular,
accepting the statement does not establish existence of the retraction.
