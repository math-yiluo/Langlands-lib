# Points of disjoint unions and of induced analytic spaces

This module computes, on points of the underlying topological spaces, the
summand inclusions of the chosen disjoint union `localizedSigmaCofan` in the
localized category of analytic spaces, and the structure morphisms of
Berkovich's induced space `X_{G/H}` (module `InducedAnalyticSpace`). It also
defines the coset of `G/H` that indexes the copy containing a point of
`X_{G/H}`. All statements are proved. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation` (the first lemma) and its
sub-namespace `InducedSpace` (everything else).

Points are elements of `localizedSpaceFunctor.obj Y`, the underlying
topological space of an object `Y` of `LocalizedCategory`. The underlying space
of the disjoint union `localizedSigma Y` is, by definition, the sigma type
`(j : J) × localizedSpaceFunctor.obj (Y j)`, so a point of `X_{G/H}` is a pair
`⟨c, x⟩` with `c : G ⧸ H` and `x` a point of `X`.

## Declarations

Disjoint unions, for `Y : J → LocalizedCategory.{u, max z v, max z v}`:

- `localizedSigmaCofan_inj_space_apply`: the inclusion of the summand `j`
  sends `x` to `⟨j, x⟩`. Proof: the inclusion is a fraction whose denominator
  is the quasi-isomorphism `nonemptyReplacementHom` and whose numerator is the
  sigma injection of presentations. The Library lemma
  `numerator_point_eq_of_fraction_equation` (module
  `NearIdentityDomainRestriction`) evaluates such a fraction on points.

Induced spaces, for a subgroup `H ≤ G` and
`X : Action (LocalizedCategory.{u, max z v, max z v}) H`:

- `copy_space_apply`, `copy_space_eq`: the inclusion `copy H X c` of the copy
  indexed by `c` is `x ↦ ⟨c, x⟩`, that is, `Sigma.mk c`.
- `copy_space_injective`, `range_copy_space`, `isOpen_range_copy_space`: this
  map is injective, its image is the image of `Sigma.mk c`, and that image is
  open.
- `actionMap_space_apply`: the action `actionMap H X g` of `g ∈ G` sends
  `⟨c, x⟩` to `⟨g • c, κ(g, c) • x⟩`, where `κ(g, c) = correction H g c ∈ H`
  is the correction cocycle of `InducedAnalyticSpace`.
- `pointCoset H X p` (definition): the first component of a point `p` of
  `X_{G/H}`, that is, the coset indexing the copy that contains `p`.
  `pointCoset_mk`: `pointCoset ⟨c, x⟩ = c`. `pointCoset_copy`: points of the
  copy `c` have coset `c`. `mem_range_copy_space_iff`: a point lies in the
  image of `copy H X c` exactly when its coset is `c`.
- `pointCoset_actionMap`: the coset of `g • p` is `g • pointCoset p`, so `g`
  maps the copy `c` into the copy `g • c`.
- `unitHom_space_apply`, `pointCoset_unitHom`: the unit
  `unitHom H X = X.ρ r⁻¹ ≫ copy H X (baseCoset H)` sends `x` to
  `⟨H, r⁻¹ • x⟩`, where `r = baseRep H ∈ H` is the chosen representative of the
  coset `H`. Its image lies in the copy indexed by `baseCoset H`.
- `inductionFunctor_map_space_apply`, `pointCoset_inductionFunctor_map`: for
  `f : X ⟶ X'`, the induced morphism `((inductionFunctor H).map f).hom`
  sends `⟨c, x⟩` to `⟨c, f x⟩`. It preserves cosets. The proof uses the
  Library lemma `copy_inductionFunctor_map`.
- `liftHom_space_apply`: for `f : X.V ⟶ Y.V` with `Y` a `G`-object, the
  extension `liftHom H f : X_{G/H} → Y` sends `⟨c, x⟩` to `c.out • f x`
  (Library lemma `copy_liftHom`).

## Original source and provenance

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1.2, printed p.2: `X′` is "the disjoint union ∐_{i∈G/H} X_i, where X_i is
a copy of X", "if gg_i = g_jh, h ∈ H, then g|_{X_i} = f_j h f_i^{-1} :
X_i → X_j", and "ϕ′|_{X_i} = g_i ϕ f_i^{-1}". The formulas here are these
descriptions, read on points of the Library's construction. The module is an
internal helper for the proof of Berkovich's Example 1.2.1(i)
(`QuasiEtaleSiteEquivalenceStatement`). The definition
`pointCoset` and the formulas are computed here and are not stated in the
source.
