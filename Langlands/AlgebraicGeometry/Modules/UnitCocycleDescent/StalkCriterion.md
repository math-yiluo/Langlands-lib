# A local unit criterion for maps from a line bundle to the structure sheaf

This helper module supports the proof of
`Langlands.Scheme.Modules.UnitCocycleDescentEffectiveStatement`. It is an
internal lemma, not a published statement, and has no separate literature
source. It is a special case of the standard fact that a morphism of
invertible sheaves that is surjective on stalks is an isomorphism: here the
target is the structure sheaf, and stalk surjectivity is phrased as the
existence of local sections sent to units.

## Statement

`Langlands.Scheme.Modules.isIso_of_isUnit_app_locally` takes a scheme `X`,
a scheme module `N` with
`Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne N`, and a morphism
`φ : N ⟶ SheafOfModules.unit X.ringCatSheaf`. It assumes that every point
`x` lies in an open `V` with a section `n` of `N` over `V` such that
`φ.app V n` is a unit of the ring `Γ(X, V)`. It concludes `IsIso φ`. The
section `φ.app V n` lies in the sections of the unit module over `V`. These
are definitionally the ring `Γ(X, V)`, and the statement writes
`IsUnit (M := Γ(X, V))` to use that ring structure. The theorem works in
the full universe `u` and adds no hypotheses on `X`.

## Proof

The published `Langlands.SchemeModule.isIso_iff_stalk_isIso` reduces the
claim to the stalk map at each point `x`. Choose a rank-one chart
`e : N.restrict U.ι ≅ unit` with `x ∈ U` and a neighbourhood `V` of `x`
with a section `n` that `φ` sends to a unit. Conjugate the restriction of
`φ` to `U` by `e` and `Scheme.Modules.restrictUnitIso U.ι`. The result is
an endomorphism `ψ` of the structure module of `U`. Functors preserve the
two conjugating isomorphisms. With the published `isIso_stalk_restrict_iff`
this shows that the stalk map of `ψ` at a point of `U` is an isomorphism
exactly when the stalk map of `φ` at its image is. This is the pattern of
`isOpen_lineBundle_stalkFrame`.

Let `W = U.ι ⁻¹ᵁ V`, whose image `U.ι ''ᵁ W` lies in `V`. Restrict `n` to
that image and let `a = e.hom.app W n'` be the restricted section `n'` in
the chart. Then `ψ.app W a` is `(U.ι.appIso W).hom` applied to
`φ.app (U.ι ''ᵁ W) n'`. By naturality of `φ` this is the image of the unit
`φ.app V n` under ring homomorphisms, so it is a unit. The published
`unitEndCoefficient_app` writes `ψ.app W a` as `a` times
`unitEndCoefficient ψ W`, so this coefficient is a unit. The published
`unitEnd_restrict_isIso` then makes the restriction of `ψ` to `W` an
isomorphism. Hence the stalk of `ψ` at the point `x` of `W` is an
isomorphism, by `isIso_stalk_restrict_iff`. By the comparison above, the
stalk of `φ` at `x` is an isomorphism.
