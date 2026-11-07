# Automorphisms of towers over levels satisfying a property, reindexed along level functors

This internal construction restricts a group action by tower automorphisms
along the reindexing of `Langlands.Shimura.RestrictedReindexLevelTowerCohomology`
and the away towers of `Langlands.Shimura.RestrictedSplitLevelTowerCohomology`.
Let `Γ` act on a tower `T` of schemes over the levels satisfying `P`, by
automorphisms over a base scheme `X`. Then `Γ` acts on the reindexed tower
`K ↦ T (Φ K)` along a level functor `Φ`, and on the away tower
`K' ↦ T (e⁻¹ (K₀ × K'))`. On colimit cohomology with coefficients pulled back
from `X`, the induced action commutes with the comparison of colimits. The
first part is in namespace `Langlands.Shimura.RestrictedReindexLevelTowerCohomology`
and the away part in namespace `Langlands.Shimura.RestrictedSplitLevelTowerCohomology`.

## Motivation and scope

The published CM modules equip the actual geometric CM tower with a Galois
action by tower automorphisms over `Spec F`. Restricting this action to the
prime-to-`m` tower
(`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`, submitted
together with this module) is an instance of the general restriction here.
The module constructs no schemes, automorphisms or coefficients. No topology
on `Γ` and no continuity of its action is considered.

## Inputs

Let `H` and `G` be groups with topologies, `φ : H →* G`,
`Φ : FunctorOver φ` a level functor over `φ` (the published
`CompactOpenLevel.FunctorOver`), `P` and `P'` properties of levels of `G` and
`H`, and `hΦ : ∀ K, P' K → P (Φ.functor.obj K)`.

The published module `Langlands.Shimura.RestrictedLevelReindex` provides
`Φ.restrictedFunctor hΦ` from the levels satisfying `P'` to the levels
satisfying `P`, the comparison of colimits
`RestrictedLevelColimit.reindexComparison Φ hΦ`, the property
`P.inverseImage Φ.functor` with `Φ.mapsTo_inverseImage`, and the instances
`isDownwardClosed_inverseImage` and `isConjStable_inverseImage`. The published
module `Langlands.Shimura.RestrictedReindexLevelTowerCohomology` provides
`reindexProjection Φ hΦ p` (the projections `p.app (Φ K)` of the reindexed
tower), `whiskerLeft_reindexProjection`, `reindex_selfArrow` and
`canonicalPullback_reindexComparison`. The published module
`Langlands.Shimura.RestrictedSplitLevelTowerCohomology` provides, for
`e : G ≃ₜ* H × H'` and a level `K₀` of `H`, the away functor
`awayFunctor e P K₀`, the away tower `awayLevelTower e K₀ T` and the
comparison `awayCohomologyComparison`; the published
`Langlands.Shimura.SplitLevelTower` provides the level functor
`awayOver e K₀`. The published module
`Langlands.Shimura.RestrictedLevelTowerCanonicalCoefficients` provides, in
namespace `RestrictedLevelTowerCohomology`,
`canonicalCoefficients R p M` and
`automorphismActionFunctor R p hT ρ hρ n`, the colimit cohomology of
coefficients pulled back from `X` as an object of
`Action (SmoothRep R G) Γ`, where `γ` acts by smooth pullback along
`(ρ γ).unop.hom`.

## Restricting automorphisms

Let `T : P.FullSubcategory ⥤ Scheme.{u}`.

- `reindexAutHom Φ hΦ T : Aut T →* Aut (Φ.restrictedFunctor hΦ ⋙ T)` is
  Mathlib's `Functor.mapAut` for whiskering on the left with
  `Φ.restrictedFunctor hΦ`. `reindexAutHom_hom` states that the restriction
  of `α` has underlying morphism
  `Functor.whiskerLeft (Φ.restrictedFunctor hΦ) α.hom`, by `rfl`.

Let `Γ : Type v` be a group and `ρ : Γ →* (Aut T)ᵐᵒᵖ`, following the
convention of the published automorphism actions.

- `reindexAutomorphisms Φ hΦ ρ : Γ →* (Aut (Φ.restrictedFunctor hΦ ⋙ T))ᵐᵒᵖ`
  is `ρ` followed by the opposite of `reindexAutHom Φ hΦ T`.
  `reindexAutomorphisms_hom` states that `γ` acts by the whiskering of
  `(ρ γ).unop.hom`, by `rfl`.
- Let `p : T ⟶ (Functor.const P.FullSubcategory).obj X` and
  `hρ : ∀ γ, (ρ γ).unop.hom ≫ p = p`. Then `reindexAutomorphisms_over Φ hΦ ρ hρ γ`
  states that the restricted automorphisms lie over `X` for the projections
  `reindexProjection Φ hΦ p`. It is `whiskerLeft_reindexProjection`.

## The action on colimit cohomology and the comparison

Assume moreover that every level map of `T` is étale, that `H` and `G` are
topological groups, that `P` and `P'` are conjugation stable, that `R : Type u`
is a commutative ring, and that `hT` states that `T.map` of each
`restrictedSelfArrow P K k hk` is the identity.

- `reindexAutomorphismActionFunctor Φ hΦ ρ hρ R hT n` is the published
  `automorphismActionFunctor` for the reindexed tower, its projections
  `reindexProjection Φ hΦ p`, the level triviality `reindex_selfArrow Φ hΦ hT`
  and the action `reindexAutomorphisms Φ hΦ ρ`. It is a functor from
  `ModuleSheaf X R` to `Action (SmoothRep R H) Γ`: the colimit over the levels
  satisfying `P'` of the degree `n` cohomology of `T (Φ K)` with coefficients
  pulled back from `X`, with the action of `Γ`.
- `automorphism_reindexComparison_apply Φ hΦ ρ hρ R hT n M γ x`: the
  comparison `RestrictedLevelColimit.reindexComparison Φ hΦ` for the
  cohomology of `canonicalCoefficients R p M` sends the action of `γ` on `x`
  to the action of `γ` on the image of `x` in
  `(automorphismActionFunctor R p hT ρ hρ n).obj M`. It is
  `canonicalPullback_reindexComparison` for `(ρ γ).unop.hom`, evaluated at `x`.

## Away towers

Let `G`, `H`, `H'` be groups with topologies, `e : G ≃ₜ* H × H'`, `P` a
property of levels of `G`, `K₀` a level of `H`, `T` a tower over the levels
satisfying `P` and `ρ : Γ →* (Aut T)ᵐᵒᵖ`. The away tower is the reindexing
along `awayOver e K₀`, with
`hΦ = (awayOver e K₀).mapsTo_inverseImage`.

- `awayAutomorphisms e K₀ ρ : Γ →* (Aut (awayLevelTower e K₀ T))ᵐᵒᵖ` is
  `reindexAutomorphisms` for this reindexing. `awayAutomorphisms_hom` states
  that `γ` acts by `Functor.whiskerLeft (awayFunctor e P K₀) (ρ γ).unop.hom`,
  by `rfl`.
- `awayAutomorphisms_over e K₀ ρ hρ γ` is `reindexAutomorphisms_over` for
  this reindexing.

Assume moreover that `G` and `H'` are topological groups, that `P` is
downward closed and conjugation stable, that the level maps of `T` are étale,
and keep `R` and `hT`.

- `awayAutomorphismActionFunctor e K₀ ρ hρ R hT n` is
  `reindexAutomorphismActionFunctor` for this reindexing, a functor from
  `ModuleSheaf X R` to `Action (SmoothRep R H') Γ`.
- `automorphism_awayComparison_apply e K₀ ρ hρ R hT n M γ x`: the comparison
  `awayCohomologyComparison e K₀ (canonicalCoefficients R p M) n` commutes
  with the action of `γ`, as in `automorphism_reindexComparison_apply`.

## Proof outline

The homomorphisms are composites of Mathlib's `Functor.mapAut` and
`MonoidHom.op`. The over-base property is `whiskerLeft_reindexProjection`.
The comparison statement is the pointwise form (`ConcreteCategory.congr_hom`)
of `canonicalPullback_reindexComparison`. The away statements apply the
general ones to `awayOver e K₀`; the conjugation stability of the away
levels comes from `isConjStable_inverseImage`.

## Provenance

This is an internal construction on the restricted reindexing and away
framework. It asserts no statement from external literature.
