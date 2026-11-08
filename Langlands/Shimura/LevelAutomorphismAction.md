# Automorphism actions on the cohomology of a tower at a fixed level

This internal construction gives the action of a group of tower
automorphisms on the cohomology of a single level. Let `T` be a tower of
schemes over the compact open levels of a topological group `G` that satisfy
a property `P`, with projections `p : T ⟶ const X` to a base scheme `X`. Let
a group `Γ` act on the tower by automorphisms over `X`, that is,
`ρ : Γ →* (Aut T)ᵐᵒᵖ` with `(ρ γ).unop.hom ≫ p = p` for every `γ`. At every
fixed level `K`, the group `Γ` then acts on the étale cohomology
`H^n(T_K, p_K^* M)` of a sheaf `M` on `X` pulled back to `T_K`. An element
`γ` acts by pullback along its automorphism of `T_K`, together with the
canonical comparison of the pulled-back coefficients along the triangle over
`X`. The action is natural in `M`. The insertion of the level-`K` cohomology
into the colimit over all levels intertwines it with the published action
of `Γ` on the colimit. The declarations are in namespace
`Langlands.Shimura.LevelAutomorphismAction`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313 concerns the action of `Gal(F̄/F)` on
the cohomology `H^{n-1}(S_K(N), W)` of the Shimura variety at the fixed
level `K(N)`, which Harris introduces on printed p. 312. The published
module `Langlands.Shimura.RestrictedLevelTowerCanonicalCoefficients`
constructs the action of a group of tower automorphisms on the colimit of
the cohomology over all levels (`automorphismAction`). This module provides
the corresponding action at one fixed level, and its compatibility with the
colimit.

The coefficients are sheaves on the base pulled back to the levels. Nothing
is assumed or proved about the action beyond the group laws, naturality and
the compatibility with the colimit: no continuity, finiteness or
unramifiedness. No statement of Harris is formalized.

## Inputs

All from the published Library:

- `Langlands.Shimura.LevelTowerCohomology.projectionCohomologyMap R q r f h n M`
  (`Langlands/Shimura/LevelTowerCanonicalCoefficients.lean`): for an étale
  `f : Y ⟶ Z` with `h : f ≫ q = r`, the pullback
  `H^n(Z, q^* M) ⟶ H^n(Y, r^* M)` with the comparison
  `f^* q^* M ≅ r^* M`. It comes with `projectionCohomologyMap_congr`, `_id`,
  `_comp` (pullbacks compose contravariantly) and `_naturality` (naturality
  in `M`).
- From `Langlands.Shimura.RestrictedLevelTowerCanonicalCoefficients`:
  `canonicalCoefficients R p M`, the coefficient diagram of the `p_K^* M`;
  `automorphismAction R p hT ρ hρ n M`, the action of `Γ` on the colimit of
  their cohomology over all levels; `canonicalPullback_ι`, which describes
  that action on the image of a level; and the instance that components of
  isomorphisms of towers are étale.
- `RestrictedLevelColimit.ι`, the insertion of a level into the colimit, and
  `restrictedSelfArrow`.

## The action at a fixed level

Let `R` be a commutative ring, `K : P.FullSubcategory` a level and `n` a
degree.

- `levelAction R p ρ hρ K n M : Action (ModuleCat R) Γ` has space
  `H^n(T_K, p_K^* M)`, that is,
  `(cohomology (T.obj K) R n).obj ((inverseImage (p.app K) R).obj M)`.
  `γ` acts by
  `projectionCohomologyMap R (p.app K) (p.app K) ((ρ γ).unop.hom.app K) _ n M`
  (`levelAction_ρ`).
- `levelActionFunctor R p ρ hρ K n : ModuleSheaf X R ⥤ Action (ModuleCat R) Γ`
  sends `M` to `levelAction R p ρ hρ K n M` (`levelActionFunctor_obj`) and a
  morphism `α` to the map induced on cohomology by `(inverseImage (p.app K) R).map α`
  (`levelActionFunctor_map_hom`).

## Comparison with the colimit over levels

Assume now that the transition maps of `T` are étale, that `T` sends the
self-arrows of each level `K` given by elements of `K` to the identity
(`hT`), that `G` is a topological group and that `P` is stable under
conjugation.

- `automorphismAction_ρ_ι_apply`: for `x` in `H^n(T_K, p_K^* M)`, the action
  of `γ` on the colimit, `(automorphismAction R p hT ρ hρ n M).ρ γ`, sends
  the image of `x` under `RestrictedLevelColimit.ι` to the image of
  `((levelAction R p ρ hρ K n M).ρ γ).hom x`.

## Proof outline

The identity laws hold because `(ρ 1).unop.hom.app K` is the identity, and
by `projectionCohomologyMap_congr` and `projectionCohomologyMap_id`. For the
multiplication law, `End.mul_def` writes the product of two endomorphisms as
their composite in the opposite order. `projectionCohomologyMap_comp` turns
the composite of two pullbacks into the pullback along the composite. The
composite `(ρ γ).unop.hom.app K ≫ (ρ δ).unop.hom.app K` is
`(ρ (γ * δ)).unop.hom.app K`, by `map_mul`, `MulOpposite.unop_mul` and
`Aut.Aut_mul_def`. Naturality in `M` is `projectionCohomologyMap_naturality`.
The comparison with the colimit is `canonicalPullback_ι` applied to an
element.

## Provenance

This is an internal construction on top of the published coefficient and
pullback constructions of `Langlands.Shimura.LevelTowerCohomology` and
`Langlands.Shimura.RestrictedLevelTowerCohomology`. It is the fixed-level
counterpart of the published `automorphismAction`. Harris (1999), printed
pp. 312-313, is motivation only.
