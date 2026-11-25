# Exact normalizer criterion for actual conjugate families

This is an internal construction and elementary consequence of the actual
conjugate-family interface. The base scheme `S`, groups `H` and `G`,
homomorphism `i : H ⟶ G`, and parameter scheme `M` are arbitrary in universe
`u`. There are no monicity, closedness, reductivity or parabolicity hypotheses.

For any refinement `a : T ⟶ M`, `familyRefinementTestIso a` identifies `T` with
the original-base test obtained by regarding `T.left` over `M.left` via `a.left`.
Its underlying scheme map is the identity, and its compatibility equation is the
equation for a morphism in `Over S`. `familyRefinementPointsEquiv a` composes the
published base-change point equivalence with this test isomorphism. It is a
multiplicative equivalence between actual points of the pulled-back group on
the relative test and actual points of `G` on `T`.

`mem_range_conjugateFamily_refinement_iff` computes membership in the actual
conjugate family using this equivalence. An original point `x` corresponds to a
point of the conjugate family precisely when `(a ≫ g)⁻¹ * x * (a ≫ g)` belongs
to `range i` on `T`. The proof transports the published membership formula
across the identity-underlying test isomorphism in both directions.

`normalizer_of_range_conjugateFamily_eq` proves the converse to the existing
normalizer-invariance result. Equality of conjugate subgroup functors gives,
for every refinement `a` and every original point `z`, equivalence of membership
of its two inverse conjugates. For a point `x` in `range i`, use respectively
`z = (a ≫ g₂) * x * (a ≫ g₂)⁻¹` and
`z = (a ≫ g₁) * x * (a ≫ g₁)⁻¹`. Group identities give preservation under
conjugation by the restricted `g₁⁻¹ * g₂` and its inverse. Since `a` was
arbitrary, this is membership in the full normalizer, rather than just a
condition on points over `M`.

`range_conjugateFamily_eq_iff` combines this converse with the existing
invariance theorem: two actual conjugate families are equal if and only if
`g₁⁻¹ * g₂` belongs to the full normalizer of `range i` on `M`. This module does
not construct a quotient scheme or assert representability of the parabolic
functor.
