# Smooth targets of faithfully flat group homomorphisms

This derived helper module isolates the smoothness step needed for
`NormalSubgroupQuotientStatement`. It constructs no quotient. It works in
arbitrary universe `u` over an arbitrary field, including imperfect fields and
positive characteristic.

`Langlands.GroupScheme.FppfHomSmoothTargetStatement.{u}` is the named
proposition: for every field `k : Type u` and every homomorphism `q : G ⟶ Q`
of group schemes over `Spec k`, smoothness of `G` together with flatness,
surjectivity and local finite presentation of `q` implies smoothness of `Q`.
`Langlands.GroupScheme.fppfHomSmoothTarget` proves this proposition using
the lemmas below. The statement has no hypothesis on the kernel.

`Langlands.AlgebraicGeometry.geometricallyReduced_of_surjective_flat_comp`
states that if `p : X ⟶ Y` is flat and surjective and `p ≫ f` is geometrically
reduced, then `f : Y ⟶ S` is geometrically reduced. The base `S` is arbitrary.
For each field-valued point of `S`, the iterated pullback isomorphism identifies
the fibre of the composite with the pullback of `p` over the fibre of `f`.
Flatness and surjectivity survive this base change. The imported
`GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective`
descends reducedness to the fibre of `f`.

`Langlands.GroupScheme.smooth_target_of_surjective_flat_hom` applies to a
homomorphism `q : G ⟶ Q` of group schemes over `Spec k`. Its assumptions are
smoothness of `G` and flatness, surjectivity and local finite presentation of
`q`. Local finite presentation of `Q` follows by source descent from that of
`G`. Smoothness of `G` implies geometric reducedness, which the preceding
lemma descends to `Q`. Mathlib's `AlgebraicGeometry.smooth_of_grpObj` then
proves smoothness of `Q`. This last theorem uses translations after extending
the field to its algebraic closure.

`Langlands.GroupScheme.RelativeRoot.IsFppfQuotient.smooth_target` applies
this construction to the published `IsFppfQuotient` predicate. The subgroup
functor may have a non-smooth representative; no kernel smoothness is used.
Neither this corollary nor its proof assumes that `G` or `Q` is affine or
connected.

The provenance is derived: these results combine the imported Library
reducedness and finite-presentation descent proofs with Mathlib's group
smoothness theorem. No new literature assertion or representability claim
is introduced.
