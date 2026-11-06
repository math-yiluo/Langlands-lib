# Galois action on colimit cohomology of towers over levels satisfying a property

This internal construction repeats the published
`Langlands.Shimura.LevelTowerGalois` for towers of schemes defined only on
the compact open levels satisfying a property `P`. It base-changes such a
tower along a ring extension `F → L` and obtains the action of `L ≃ₐ[F] L`
on the colimit over levels satisfying `P` of étale cohomology of the
base-changed tower, with coefficients pulled back from a base of the original
tower. The action is by morphisms of smooth `G`-representations, so it
commutes with the action of `G`. For a tower over all levels, the module
identifies this for its restriction with the published construction over all
levels. All declarations are in namespace
`Langlands.Shimura.RestrictedLevelTowerGalois`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, studies the cohomology of a tower of Shimura varieties over a number
field, base-changed to an algebraic closure, with commuting actions of the
finite adelic group and of the Galois group: after (3.5) on printed p. 307,
and in Proposition 4.10 on printed p. 311 for `GG(A_f^{ℓ,p})` as
`K(N)^{ℓ,p}` varies. When the tower is only constructed for sufficiently
small levels, it is a functor on a full subcategory of levels, which is the
situation treated here. Harris's passages are motivation only; no statement
from them is formalized.

The module constructs no Shimura varieties, no particular property of
levels, and none of Harris's automorphic coefficient systems. It proves no
topology on `L ≃ₐ[F] L` and no continuity of its action, and makes no
comparison of the base change to `L` with the colimit over finite
subextensions or with the cohomology of a limit scheme.

## Inputs

Let `G : Type u` be a group with a topology,
`P : ObjectProperty (CompactOpenLevel G)` and
`T : P.FullSubcategory ⥤ Scheme.{u}`. Let `F` and `L` be commutative rings in
universe `u` with `Algebra F L`, and let
`s : T ⟶ (Functor.const P.FullSubcategory).obj (Spec F)` be structure maps,
so that `T.map a ≫ s_V = s_U` for `a : U ⟶ V` (`structure_naturality`).

## The base-changed tower and its Galois automorphisms

- `baseChangeTower F L s` sends a level `U` to the published
  `baseChange F L s_U = T(U) ×_{Spec F} Spec L`, and an arrow `a` to the map
  of fiber products given by `T.map a` and the identity of `Spec L`.
  `baseChangeTower_map_fst` and `baseChangeTower_map_snd` record its two
  projections. `etale_baseChangeTower_map` states that its level maps are
  étale when those of `T` are, by Mathlib's `MorphismProperty.pullbackMap`.
- `baseChangeProjection F L s : baseChangeTower F L s ⟶ T` is the first
  projection. `baseChangeTower_selfArrow` transfers the level-triviality
  hypothesis `T.map (restrictedSelfArrow P U k hk) = 𝟙` to the base change.
- `towerGaloisAut s σ` is the automorphism of the base-changed tower with
  components the published `baseChangeAut s_U σ` (`towerGaloisAut_hom_app`),
  and `towerGaloisAction F L s : (L ≃ₐ[F] L) →* (Aut (baseChangeTower F L s))ᵐᵒᵖ`
  assembles them, using the published `baseChangeMap_one` and
  `baseChangeMap_comp` (`towerGaloisAction_hom_app`). The opposite group is
  used because morphisms of spectra compose contravariantly.
- `towerGaloisAction_over s p` states, for projections
  `p : T ⟶ (Functor.const P.FullSubcategory).obj X`, that every Galois
  automorphism lies over `X` through `baseChangeProjection F L s ≫ p`.

For a tower `T₀` over all levels with structure maps `s₀`,
`baseChangeTower_restrict` states, by `rfl`, that the base change of the
restricted tower `P.ι ⋙ T₀`, with structure maps `restrictProjection P s₀`,
is the restriction `P.ι ⋙ LevelTowerGalois.baseChangeTower F L s₀` of the
published base-changed tower. `towerGaloisAction_restrict` states, by `rfl`,
that its Galois automorphisms are the restrictions
`Functor.whiskerLeft P.ι` of the published ones.

## Colimit cohomology with the Galois action

Assume that the level maps of `T` are étale, that `G` is a topological group
and `IsConjStable P`. Let `R : Type u` be a commutative ring and `hT` the
level-triviality hypothesis for `T`.

- `galoisCohomologyFunctor F L s p R hT n : ModuleSheaf X R ⥤
  Action (SmoothRep R G) (L ≃ₐ[F] L)` is the `automorphismActionFunctor` of
  `RestrictedLevelTowerCanonicalCoefficients` for the base-changed tower, its
  projections `baseChangeProjection F L s ≫ p` and `towerGaloisAction F L s`.
  Its underlying smooth representation is the colimit over shrinking levels
  `U` satisfying `P` of `H^n(T(U) ×_{Spec F} Spec L, (p_U ∘ pr₁)^* M)`
  (`galoisCohomologyForgetIso`).
- `galoisCohomologyFunctor_ρ` states that `σ` acts by the smooth pullback
  along `towerGaloisAut s σ`.

## Comparison with towers over all levels

Let `T₀ : CompactOpenLevel G ⥤ Scheme.{u}` have étale level maps, structure
maps `s₀` to `Spec F`, projections `p₀` to `X`, and the published
level-triviality hypothesis `hT₀`. Assume `IsDownwardClosed P` and
`Nonempty P.FullSubcategory` in addition to the hypotheses above.

- `galoisCohomologyRestrictIso F L s₀ p₀ R hT₀ n` is a natural isomorphism
  from `galoisCohomologyFunctor F L (restrictProjection P s₀)
  (restrictProjection P p₀) R (restrict_selfArrow hT₀) n` to the published
  `LevelTowerGalois.galoisCohomologyFunctor F L s₀ p₀ R hT₀ n`, in
  `Action (SmoothRep R G) (L ≃ₐ[F] L)`. It is
  `automorphismActionRestrictIso` for the published base-changed tower, with
  compatibility `towerGaloisAction_restrict`.

## Provenance

This is an internal construction from published results: `baseChange`,
`baseChangeMap`, `baseChangeAut` and their laws in `EtaleGaloisAction`; the
published `LevelTowerGalois` base-changed tower and Galois action for the
comparison; and Mathlib's fiber products and `MorphismProperty.pullbackMap`.
It uses the automorphism actions and their comparison from
`RestrictedLevelTowerCanonicalCoefficients`. No action, smoothness or
compatibility is supplied as input. Harris's passages are cited only as
motivation.
