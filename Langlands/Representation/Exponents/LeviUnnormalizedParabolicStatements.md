# The unnormalized parabolic functors `Ind_P^G` and `j_N`: statements

Module `Langlands.Representation.Exponents.LeviUnnormalizedParabolicStatements`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`.
Entry proposition `LeviUnnormalizedParabolicStatements`; nothing is proved
here.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.1.1–VI.1.3, printed pp.134–136 / PDF pp.140–142. The
assertions stated here are all of VI.1.1 (printed pp.134–135 / PDF
pp.140–141).

Let `P = MN` be a parabolic subgroup of `G`. The functor
`j_N : M(G) → M(M)`, `(π, V) ↦ (π_N, V_N)`, is the restriction to `P`
followed by the `N`-coinvariants. For a smooth representation `(τ, E)` of `M`,
`Ind_P^G(τ, E)` is the smooth induction from `P` to `G` of the trivial
extension of `τ` to `P` (`τ(mn) = τ(m)`). The section then states:

> **Théorème.** Le foncteur `j_N : (π, V) ↦ (π_N, V_N)` de `M(G)` dans `M(M)`
> est l'adjoint à gauche du foncteur d'induction `Ind_P^G`. Pour toute
> représentation lisse `(τ, E)` de `M` et toute représentation lisse `(π, V)`
> de `G`, on a un isomorphisme naturel
> `Hom_M((π_N, V_N), (τ, E)) ≃ Hom_G((π, V), Ind_P^G(τ, E))`.
> Les foncteurs `Ind_P^G` et `j_N` sont exacts.

> **Corollaire.** Le foncteur `j_N` préserve les colimites et le foncteur
> `Ind_P^G` préserve les limites.

> **Remarque.** Il se trouve que `Ind_P^G` admet aussi un adjoint à droite.
> […] Par conséquent, `Ind_P^G` préserve les colimites.

The Remark's argument uses that `G/P` is compact (Lemma III.2.3), Theorem
III.2.6 and Remark 3 of III.1.15.

The normalized versions (VI.1.2) are already published for the same interface:
`LeviFrobeniusReciprocityStatement`, `LeviParabolicFunctorsExactStatement` and
`LeviParabolicFunctorsPreserveLimitsStatement` (Worker 6). Their Markdown
records that "the unnormalized Theorem of VI.1.1 is not stated separately";
this unit states it.

## Common data

Every statement quantifies over the same data as the published VI.1.2
statements:

- a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local
  field of any characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`, with
  `hG.isAffineHom` and the canonical topology
  `RationalPointFamily.pointTopology` on `rationalPoints G`, and the hypotheses
  `[LocallyCompactSpace (rationalPoints G)]` and
  `[NonarchimedeanGroup (rationalPoints G)]` for that topology;
- every actual rational parabolic `p : P ⟶ G` (`hp : IsParabolicSubgroup p`),
  rational Levi `l : M ⟶ P` (`hl : IsRationalLeviSubgroup l`) and matching
  geometric unipotent radical `r : U ⟶ P`
  (`hr : LeviSubgroup.IsGeometricUnipotentRadical r`,
  `hmul : IsIso (subgroupMultiplication l r)`);
- on `rationalPoints M`, the topology `leviPointTopology l hl` with local
  compactness and the nonarchimedean-group property derived by
  `leviPoints_locallyCompactSpace` and `leviPoints_nonarchimedeanGroup`.

`M(G)` and `M(M)` are `SmoothRep ℂ (rationalPoints G)` and
`SmoothRep ℂ (rationalPoints M)`.

## The objects

No new construction is introduced; the two functors are published objects or
composites of published functors.

- `j_N` is the published `leviUnnormalizedJacquetFunctor p l r hp hr hl`: the
  actual coinvariants `V_N` for the radical image `pointImage (r ≫ p)`
  (`Jacquet.Localization.smoothFunctor` with the trivial character), with the
  descended action of the Levi image, pulled back along
  `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)`. A Levi point `m`
  sends the class `[x]` to `[π(m) x]`; there is no twist. The published
  `leviJacquetFunctor_obj_representation_twist` shows that the normalized
  `r_P^G` is this functor twisted by the Haar modulus character.
- `Ind_P^G` is written inside the statements as the composite
  `SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙ inflationFunctor h ⋙ Induction.smoothInductionFunctor (pointImage p)`,
  where `h` is the published decomposition
  `isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul` of
  the parabolic image. A representation `σ` of `M(F)` is pulled back to the
  Levi image, inflated to `P(F)` along the Levi projection
  (`inflationFunctor h`, Renard's trivial extension `τ(mn) = τ(m)`), and
  smoothly induced to `G(F)` with no normalizing character. Its space consists
  of the smooth functions `f : G(F) → E` with `f(x g) = σ'(proj x) f(g)`, and
  `Induction.eval (pointImage p) _ f 1` is `f(1)`. The carrier universe `v`
  becomes `max u v`. The published normalized `leviInductionFunctor` is the
  same composite with the twist by `δ^{1/2}` before induction.

## The Lean statements

### `LeviUnnormalizedFrobeniusReciprocityStatement` (Theorem, adjunction)

For every `π : SmoothRep.{0, u, w} ℂ (rationalPoints G)` and every
`σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)`, with independent carrier
universes `w` and `v`, write `σP` for the inflated pull-back of `σ`. There is a
`ℂ`-linear equivalence

`e : Hom_G(π, Ind_P^G σ) ≃ₗ[ℂ] Hom_M(π_N, σ)`

of intertwiner spaces (`Representation.IntertwiningMap`) such that
`e F [x] = (F x)(1)` for every intertwiner `F` and every `x` in the carrier of
`π`. Here `[x]` is `Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x`
and `(F x)(1)` is `Induction.eval (pointImage p) σP.ρ (F x) 1`.

This is the Theorem's natural isomorphism in explicit form, read in the
direction `Hom_G → Hom_M`. The classes `[x]` exhaust `V_N`, so the formula
determines `e`, and naturality in `π` and `σ` follows from it (both sides of
naturality are computed by the same evaluation). As in the published
`LeviFrobeniusReciprocityStatement`, naturality is not stated as a separate
clause.

### `LeviUnnormalizedFunctorsExactStatement` (Theorem, exactness)

`Ind_P^G` sends every actual short exact sequence
(`SmoothRep.IsShortExact`) of smooth representations of `M(F)` in universe `v`
to a short exact sequence, and so does `j_N` for smooth representations of
`G(F)` in universe `v`. This is "Les foncteurs `Ind_P^G` et `j_N` sont
exacts", in the form of the published `LeviParabolicFunctorsExactStatement`.

### `LeviUnnormalizedFunctorsPreserveLimitsStatement` (Corollary and Remark)

`j_N` preserves colimits, and `Ind_P^G` preserves limits (Corollary) and
colimits (Remark), for diagrams with index categories and morphisms in
`Type v` (`PreservesColimitsOfSize.{v, v}`, `PreservesLimitsOfSize.{v, v}`).
The explicit sizes are needed because `Ind_P^G` changes the carrier universe,
as in the published `LeviParabolicFunctorsPreserveLimitsStatement`.

The Remark's first sentence, that `Ind_P^G` has a right adjoint, is not stated
as a categorical adjunction. The source builds that adjoint from `I_M^P`, the
pseudo-forgetful functor and a twist, none of which is a published functor on
this interface, and `Ind_P^G` here changes the carrier universe from `v` to
`max u v`. The Remark's conclusion, colimit preservation, is stated.

### `LeviUnnormalizedParabolicStatements`

The conjunction of the three statements, with universes `u` (field), `v` and
`w` (carriers).

## Faithfulness notes

- The statements are posed for every parabolic `P = MN`, as in the source,
  through actual rational parabolics with a rational Levi and a matching
  radical; no standardness, root presentation or Iwahori decomposition is
  assumed.
- No admissibility, finite length or finite type is assumed.
- The local compactness and nonarchimedean structure of `G(F)` are hypotheses,
  as in the published interface; those of `M(F)` are derived.
- The exactness of `j_N` uses that `N(F)` is a union of compact open subgroups
  (Corollary III.2.9 and V.5.2); this is part of what a proof must supply, not
  a hypothesis.

## Scope

This file states the assertions and proves none of them. Proofs belong to a
separate `lean.proof@1` task targeting `LeviUnnormalizedParabolicStatements`.
A route: Frobenius reciprocity for smooth induction from the closed subgroup
`P(F)` (III.2.5) composed with the factorization of `P(F)`-maps into an
inflated representation through `V_N`; exactness of coinvariants for a union
of compact open subgroups; Mathlib's limit preservation by adjoints after
universe care. The published normalized proofs and the twist identity
`leviJacquetFunctor_obj_representation_twist` can be reused.

The file imports `Langlands.Representation.Exponents.LeviJacquetCompletionNormalization`
(for `leviUnnormalizedJacquetFunctor`),
`Langlands.Representation.Smooth.FiniteLengthGrothendieck` (for
`SmoothRep.IsShortExact`) and `Langlands.GroupScheme.Reductive.Basic`
(environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
