# Fixed vectors of level-tower cohomology as modules over Hecke algebras

This internal construction makes the `K`-fixed vectors of the published
colimit cohomology of level towers into modules over the Hecke algebra
`LevelHeckeAlgebra R K` of `Langlands.Shimura.LevelHeckeAlgebra`. The action
of a group of tower automorphisms, or of `E ≃ₐ[F] E` on the cohomology of a
base change, is by module maps, so it commutes with every element of the
Hecke algebra, not only with the individual double-coset operators of
`Langlands.Shimura.LevelHeckeAction`. Restricting the scalars back to `R`
recovers the fixed-vector functors of `LevelHeckeAction`. The same holds for
towers defined only on the levels satisfying a property `P`, and for the
restriction of a tower over all levels these Hecke-modules agree with those
over all levels. All declarations are in namespace
`Langlands.Shimura.LevelHecke`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, studies the cohomology of Shimura varieties together with commuting
actions of the Galois group and of the finite adelic group (printed p. 307
after (3.5); Proposition 4.10, printed p. 311). At a fixed level `K`, the
finite adelic group acts through the Hecke algebra of `K`. This module
records that structure, and its commutation with the Galois action, for the
constructions available in the Library. Harris's passages are motivation
only; no statement from them is formalized.

The module does not identify the `K`-fixed vectors of colimit cohomology
with the cohomology at level `K`, and it computes no structure constants of
the Hecke algebra. It proves no continuity of the Galois action and makes no
comparison with the complex Haar-measure Hecke algebras of
`Langlands.Representation.Hecke`.

## Hecke-modules with an action

Let `R : Type t` be a commutative ring, `G : Type v` a group with a topology,
and `K : Subgroup G`. The published `heckeModuleFunctor R K` of
`LevelHeckeAlgebra` sends a smooth representation to its `K`-fixed vectors as
a module over `LevelHeckeAlgebra R K`.

- `heckeModuleForgetIso R K` is the isomorphism between the composite of
  `heckeModuleFunctor R K` with `ModuleCat.restrictScalars` along
  `algebraMap R (LevelHeckeAlgebra R K)` and the fixed-vector functor
  `fixedVectorsFunctor R K` of `LevelHecke`. Its components are the identity
  on the underlying vectors. They are `R`-linear because the Hecke algebra
  acts compatibly with `R` (the `IsScalarTower` instance of
  `LevelHeckeAlgebra`, used through `algebraMap_smul`).

Let `Γ : Type u''` be a monoid. An object of `Action (SmoothRep R G) Γ` is a
smooth representation on which `Γ` acts by morphisms of smooth
representations.

- `heckeModuleActionFunctor R Γ K` is Mathlib's `Functor.mapAction` of
  `heckeModuleFunctor R K`. It sends such an object to its `K`-fixed vectors
  as a Hecke-module, on which `γ` acts by the restriction of the action of
  `γ`, now a map of Hecke-modules. `heckeModuleActionFunctor_smul` states
  that `a • x` is `heckeAct ρ K K a x`, and
  `heckeModuleActionFunctor_ρ_smul` that the action of each `γ` commutes with
  each `a : LevelHeckeAlgebra R K`.
- `heckeModuleActionForgetIso R Γ K` is the isomorphism between the
  composite of `heckeModuleActionFunctor R Γ K` with the `mapAction` of the
  restriction of scalars and `fixedVectorsActionFunctor R Γ K` of
  `LevelHeckeAction`. It is built from Mathlib's `Functor.mapActionComp` and
  `Functor.mapActionCongr` applied to `heckeModuleForgetIso`.
- For a topological group `G`, a compact open level `K` and `g : G`,
  `doubleCoset_smul_heckeActionNatTrans` states that the element
  `doubleCoset K g` of the Hecke algebra acts on `K`-fixed vectors as the
  component of `heckeActionNatTrans R Γ K K g`, that is, as the double-coset
  operator `[K g K]`.

## Level towers

Let `G : Type u` be a topological group, `T : CompactOpenLevel G ⥤ Scheme.{u}`
a tower with étale level maps, `R : Type u` a commutative ring, `X` a scheme,
`p : T ⟶ (Functor.const _).obj X` projections, `hT` the published
level-triviality hypothesis `T.map (selfArrow K k hk) = 𝟙`, and `K` a compact
open level.

- For a group `Γ` acting on `T` by automorphisms over `X`, through
  `ρ : Γ →* (Aut T)ᵐᵒᵖ` with `hρ`,
  `automorphismHeckeModuleFunctor R p hT K ρ hρ n` is the composite of the
  published `automorphismActionFunctor R p hT ρ hρ n` of
  `LevelTowerCanonicalCoefficients` with `heckeModuleActionFunctor`. It sends
  a module sheaf `M` on `X` to the `K`-fixed vectors of the colimit over
  levels of `H^n(T(U), p_U^* M)`, as a module over `LevelHeckeAlgebra R K`
  with the commuting action of `Γ`.
  `automorphismHeckeModuleForgetIso` identifies its restriction of scalars to
  `R` with `automorphismFixedFunctor R p hT K ρ hρ n` of `LevelHeckeAction`,
  and `automorphismHeckeModule_doubleCoset_smul` states that
  `doubleCoset K g` acts as the component of
  `automorphismHecke R p hT K K g ρ hρ n`.
- For commutative rings `F`, `E` with `Algebra F E` and structure maps
  `s : T ⟶ (Functor.const _).obj (Spec F)`,
  `galoisHeckeModuleFunctor R p hT K F E s n` is the composite of the
  published `LevelTowerGalois.galoisCohomologyFunctor F E s p R hT n` with
  `heckeModuleActionFunctor`. It sends `M` to the `K`-fixed vectors of the
  colimit over levels of `H^n(T(U) ×_{Spec F} Spec E, (p_U ∘ pr₁)^* M)`, as a
  Hecke-module with the action of `E ≃ₐ[F] E`.
  `galoisHeckeModuleForgetIso` identifies its restriction of scalars with
  `galoisFixedFunctor R p hT K F E s n`, `galoisHeckeModule_ρ_smul` states
  that every `σ : E ≃ₐ[F] E` commutes with every element of the Hecke
  algebra, and `galoisHeckeModule_doubleCoset_smul` that `doubleCoset K g`
  acts as the component of `galoisHecke R p hT K K g F E s n`.

## Towers over levels satisfying a property

Let `P : ObjectProperty (CompactOpenLevel G)` be stable under conjugation
(`IsConjStable P`), and let `T : P.FullSubcategory ⥤ Scheme.{u}` be a tower
over the levels satisfying `P`, with étale level maps, projections `p` to
`X`, and the level-triviality hypothesis `hT` stated with
`restrictedSelfArrow`. The level `K` need not satisfy `P`.

- `restrictedAutomorphismHeckeModuleFunctor R p hT K ρ hρ n` composes
  `RestrictedLevelTowerCohomology.automorphismActionFunctor` (from
  `RestrictedLevelTowerCanonicalCoefficients`) with
  `heckeModuleActionFunctor`: it sends `M` to the `K`-fixed vectors of the
  colimit over levels `U` satisfying `P` of `H^n(T(U), p_U^* M)`, as a
  Hecke-module with the action of `Γ`.
  `restrictedAutomorphismHeckeModuleForgetIso` identifies its restriction of
  scalars with `restrictedAutomorphismFixedFunctor` of `LevelHeckeAction`, and
  `restrictedAutomorphismHeckeModule_doubleCoset_smul` states that
  `doubleCoset K g` acts as the component of
  `restrictedAutomorphismHecke R p hT K K g ρ hρ n`.
- `restrictedGaloisHeckeModuleFunctor R p hT K F E s n` composes
  `RestrictedLevelTowerGalois.galoisCohomologyFunctor F E s p R hT n` with
  `heckeModuleActionFunctor`, for structure maps
  `s : T ⟶ (Functor.const _).obj (Spec F)`.
  `restrictedGaloisHeckeModuleForgetIso` identifies its restriction of
  scalars with `restrictedGaloisFixedFunctor`,
  `restrictedGaloisHeckeModule_ρ_smul` states that every `σ : E ≃ₐ[F] E`
  commutes with every element of the Hecke algebra, and
  `restrictedGaloisHeckeModule_doubleCoset_smul` that `doubleCoset K g` acts
  as the component of `restrictedGaloisHecke R p hT K K g F E s n`.

### Comparison with towers over all levels

Assume in addition that `P` is downward closed (`IsDownwardClosed P`) and
holds for some level (`Nonempty P.FullSubcategory`). Let `T₀` be a tower over
all compact open levels with étale level maps, projections `p₀` and
level-triviality `hT₀`, and restrict it to `P.ι ⋙ T₀` with the published
`restrictProjection P p₀` and `restrict_selfArrow hT₀`.

- Given an action `ρ₀` of `Γ` on `T₀` over `X` and an action `ρ` on the
  restriction over `X` with `hρρ₀ : (ρ γ).unop.hom =
  Functor.whiskerLeft P.ι (ρ₀ γ).unop.hom`,
  `restrictedAutomorphismHeckeModuleRestrictIso R p₀ hT₀ K ρ₀ hρ₀ ρ hρ hρρ₀ n`
  is an isomorphism from `restrictedAutomorphismHeckeModuleFunctor` of the
  restricted tower to `automorphismHeckeModuleFunctor R p₀ hT₀ K ρ₀ hρ₀ n`.
  It is the published `automorphismActionRestrictIso` whiskered with
  `heckeModuleActionFunctor`.
- For structure maps `s₀` of `T₀` over `Spec F`,
  `restrictedGaloisHeckeModuleRestrictIso R p₀ hT₀ K F E s₀ n` is an
  isomorphism from `restrictedGaloisHeckeModuleFunctor` of the restricted
  tower (with structure maps `restrictProjection P s₀`) to
  `galoisHeckeModuleFunctor R p₀ hT₀ K F E s₀ n`. It is the published
  `RestrictedLevelTowerGalois.galoisCohomologyRestrictIso` whiskered with
  `heckeModuleActionFunctor`.

Since these are isomorphisms in categories of `Action`s on Hecke-modules,
they are linear over the Hecke algebra and equivariant for `Γ` or for
`E ≃ₐ[F] E`.

## Provenance

This is an internal construction from Mathlib's `Functor.mapAction`,
`Functor.mapActionComp`, `Functor.mapActionCongr`,
`ModuleCat.restrictScalars`, `algebraMap_smul`, `NatIso.ofComponents` and
whiskering, together with `heckeModuleFunctor`, `LevelHeckeAlgebra`,
`heckeAct`, `doubleCoset` and `doubleCoset_smul` of
`Langlands.Shimura.LevelHeckeAlgebra`, the fixed-vector functors and
double-coset natural transformations of `Langlands.Shimura.LevelHecke` and
`Langlands.Shimura.LevelHeckeAction`, the published
`automorphismActionFunctor` and `LevelTowerGalois.galoisCohomologyFunctor`,
and their restricted versions and comparison isomorphisms in
`RestrictedLevelTowerCanonicalCoefficients` and
`RestrictedLevelTowerGalois`. No module structure, action, commutation or
comparison is supplied as input. Harris's passages are cited only as
motivation.
