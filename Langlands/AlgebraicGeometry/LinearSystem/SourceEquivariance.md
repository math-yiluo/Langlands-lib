# Source equivariance of linear-system morphisms

For a morphism `f : Y ⟶ X`, line bundles `L` on `X` and `M` on `Y`, and
an actual module-sheaf isomorphism `f*L ≅ M`, `transportedPullbackSections`
pulls back each ordered global section of `L` and applies that isomorphism.
If the original sections generate at every scheme point, the transported
sections do too. The actual projective-space morphism they define equals
the original linear-system morphism precomposed with `f`. The relative
version allows arbitrary base schemes and a compatible change of base.

For a scheme over `Spec K`, with `K` any commutative ring, the equivariance
lemma takes a source endomorphism over `Spec K`, a module-sheaf
isomorphism `f*L ≅ L`, and an invertible linear map on `K^(n+1)`. If
transported pullback carries the ordered sections to their specified
linear coordinate change, the actual scheme morphisms satisfy
`f ≫ linearSystemMap = linearSystemMap ≫ linearAction`. Neither `f` nor
the line bundle is replaced by its effect on points; the conclusion is
equality of scheme morphisms.

This is an internal derived construction. Generation follows by composing
the existing pullback and isomorphism-transport results. The comparison of
morphisms composes `linearSystemMap_mapIso` with
`linearSystemMap_pullback`, and its relative version uses the corresponding
relative lemmas. Finally the section equality and the condition on the
base identify the transported morphism with that for the changed
sections; `linearSystemMap_linearChange` identifies the latter with the
actual projective linear action. No additional external source assertion
is used. This unit supplies an equivariance comparison and does not assert
representability of a moduli functor.
