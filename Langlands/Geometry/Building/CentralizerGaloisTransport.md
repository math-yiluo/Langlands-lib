# Coefficient transport of full centralizer compatibility

This module shows that the coefficient action of `K ≃ₐ[k] K` on root-function
families preserves the full centralizer condition (the V6 condition of the
existing `IsCentralizerCompatible`). The order valuation must be invariant under
the coefficient automorphism. It also shows that the actual coefficient image of
a supplied KP apartment class satisfies `IsOmegaCompatible` for the
scalar-extended centralizer datum whenever the original class does. These are
internal consequences of the imported centralizer valuation, character action,
root-group transport and family-action laws. No original-source result is
asserted beyond them.

## Valuation covariance

Fix fields `k` and `K` in any universe `u`, an algebra `k → K`, a commutative
group scheme `T` over `k`, a group scheme `Z` over `k` and `s : T.toGrp ⟶ Z`.
Write `T_K` and `s_K` for the scalar extensions along `algebraBaseMap k K`.

`characterRestriction_galoisRepresentation` states that restriction of actual
rational characters of `Z_K` along `s_K` intertwines
`rationalCharacters.galoisRepresentation k K Z σ` with
`characterLattice.galoisRepresentation k K T σ`. The proof unfolds
`Cartan.characterRestriction` and applies
`rationalCharacters.characterRestrict_galoisRepresentation`.

Let `w` be a `WithZero (Multiplicative ℤ)`-valued valuation on `K`, and suppose
that `order w (σ t) = order w t` for every unit `t`. Let `hK` be bijectivity of
`Cartan.restrictionEvaluation s_K`, the hypothesis under which the existing
`centralizerValuation` is defined. `centralizerValuation_galois` proves, for every
`K`-point `z` of `Z`,

`(centralizerValuation w s_K hK (rationalConjugate k K Z σ z)).toAdd =
  galoisCocharacterAction k K T σ (centralizerValuation w s_K hK z).toAdd`.

By injectivity of `Cartan.restrictionEvaluation s_K`, it suffices to compare
evaluations against every restricted character `χ`. On the left,
`centralizerValuation_spec` gives `order w (χ (σ z))`. On the right,
`eval_galoisCocharacterAction_right`, the restriction equivariance above and
`centralizerValuation_spec` give `order w ((σ⁻¹ χ) z)` transported by `σ`.
`rationalCharacterEval_rationalConjugate` and invariance of the order identify
the two. `centralizerTranslation_galois` derives the same formula for the
negative translation `centralizerTranslation`, using linearity of the
cocharacter action.

## Generic pullback

Over any field `L`, let `S` be a commutative group scheme, `H` and `Z` group
schemes with `H` affine over the base, and `i`, `j`, `s` and `h` as in
`IsCentralizerCompatible`. The theorem `IsCentralizerCompatible.pullbackTransport`
takes:

- a centralizer-compatible family `φ`,
- a character map `α`,
- a homomorphism `β` of ambient rational points, and
- a map of centralizer points.

Suppose `ψ a g = φ (α a) (β g)`, `α` preserves relative roots, `β` maps the root
group of `a` into that of `α a`, `β` commutes with `j` through the centralizer
map, and the evaluations of translations correspond. Then `ψ` is centralizer
compatible. The proof applies the condition for `φ` at the transported data and
rewrites with these equalities.

## Coefficient action

Now let `G` and `Z` be group schemes over `k`, `G` with affine structural
morphism, and let `i : T.toGrp ⟶ G`, `j : Z ⟶ G` and `s : T.toGrp ⟶ Z`. The
private instance `extendedAffine` obtains affineness of `G_K` by base change. For
an order-invariant `σ`, `IsCentralizerCompatible.galoisTransport_inv` shows that
`RootFunctionFamily.galoisAction k K T G σ⁻¹ φ` is compatible with
`i_K`, `j_K`, `s_K` whenever `φ` is. It instantiates the generic pullback with:

- the character action of `σ`,
- `rationalConjugate k K G σ` on ambient points, and
- `rationalConjugate k K Z σ` on centralizer points.

The required hypotheses are supplied by:

- `RootFunctionFamily.galoisAction_inv_apply`,
- `mem_roots_galois_iff`,
- `RelativeRoot.rationalConjugate_mem_subgroup_iff`,
- `rationalConjugate_map`, and
- `centralizerTranslation_galois` with `eval_galoisCocharacterAction`.

`IsCentralizerCompatible.galoisTransport` gives the same result for the action
of `σ` itself. It applies the inverse statement to `σ⁻¹`, whose order invariance
follows from `invariant_apply_of_inverse` and `units_map_algEquiv_inv`.

The definition `IsCentralizerCompatible.galoisEquiv` is the resulting
permutation of the subtype of all fully centralizer-compatible families. It
applies the coefficient action of `σ`, and its inverse applies that of `σ⁻¹`.
The inverse laws follow from the group-action laws of
`RootFunctionFamily.galoisAction`. `IsCentralizerCompatible.galoisEquiv_val`
records the underlying-family formula.

## Image classes

Assume, in addition, that the underlying morphism of schemes of `i_K` is a
monomorphism. Let `D : KPApartmentData i_K (order w)` be any supplied class. Let
`C` be the scalar-extended centralizer datum with group `Z_K`, morphism `j_K` with
closed-subgroup proof `hcl`, representing proof `hrep` of `torusCentralizer i_K`, morphism `s_K`,
factorization `s_K ≫ j_K = i_K` and bijectivity `hK`.
`IsOmegaCompatible.galoisImage` proves that if `D` is `IsOmegaCompatible` for `C`,
then so is `KPApartmentData.galoisImage k K i D σ hw`. Every member of the image
class is the coefficient image of a member of `D`, so
`IsCentralizerCompatible.galoisTransport` applies.

## Scope

All results are conditional on order invariance of `σ` and on the supplied
bijectivity, closedness and representation hypotheses. The module does not prove
that the image class equals `D`. It also proves no existence or uniqueness of a
compatible valuation or apartment, and no metric, specialness or
integral-model comparison.
