# Double-coset operators commuting with automorphism and Galois actions

This internal construction shows that the double-coset operators `[K g L]`
of `Langlands.Shimura.LevelHecke` commute with any action of a monoid `Γ` on
a smooth representation by morphisms of smooth representations. It applies
this to the published colimit cohomology of level towers: the `K`-fixed
vectors of the colimit cohomology of a tower base-changed along `F → E`
carry the action of `E ≃ₐ[F] E`, and the double-coset operators between
them are equivariant, naturally in the base sheaf. The same holds for towers
defined only on the levels satisfying a property `P`, and for the restriction
of a tower over all levels these constructions agree with those over all
levels. All declarations are in namespace `Langlands.Shimura.LevelHecke`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, studies Galois representations on the cohomology of Shimura
varieties, which carries commuting actions of the Galois group and of the
finite adelic group (printed p. 307 after (3.5); Proposition 4.10, printed
p. 311). At a fixed level, the finite adelic group acts through double-coset
operators, and these commute with the Galois action. This module records
that commutation for the constructions available in the Library. Harris's
passages are motivation only; no statement from them is formalized.

The module does not identify the `K`-fixed vectors of colimit cohomology with
the cohomology at level `K`, does not construct the Hecke algebra or its
multiplication, and proves no continuity of the Galois action.

## Fixed vectors with an action

Let `R : Type t` be a commutative ring, `G : Type v` a group with a topology,
and `Γ : Type u''` a monoid. An object of `Action (SmoothRep R G) Γ` is a
smooth representation on which `Γ` acts by morphisms of smooth
representations.

- `fixedVectorsActionFunctor R Γ H` is Mathlib's `Functor.mapAction` of the
  fixed-vector functor `fixedVectorsFunctor R H` of `LevelHecke`. It sends
  such an object to its `H`-fixed vectors, on which `γ` acts by the
  restriction `fixedVectorsMap` of the action of `γ`
  (`fixedVectorsActionFunctor_obj_ρ`).

Assume that `G` is a topological group, and let `K`, `L` be compact open
levels and `g ∈ G`.

- `heckeActionNatTrans R Γ K L g` is a natural transformation from
  `fixedVectorsActionFunctor R Γ L.subgroup` to
  `fixedVectorsActionFunctor R Γ K.subgroup`. Its component at `A` is the
  double-coset operator `heckeOperator A.V.obj.ρ K L g`
  (`heckeActionNatTrans_app_hom`). The equivariance for each `γ`, and the
  naturality in `A`, are both instances of the naturality of `heckeNatTrans`
  of `LevelHecke`, applied to the morphism `A.ρ γ` or to the underlying
  morphism of smooth representations. `heckeActionNatTrans_self` states that
  `[K 1 K]` is the identity.

## Level towers

Let `G : Type u` be a topological group, `T : CompactOpenLevel G ⥤ Scheme.{u}`
a tower with étale level maps, `R : Type u` a commutative ring, `X` a scheme,
`p : T ⟶ (Functor.const _).obj X` projections and `hT` the published
level-triviality hypothesis `T.map (selfArrow K k hk) = 𝟙`.

- For a group `Γ` acting on `T` by automorphisms over `X`, through
  `ρ : Γ →* (Aut T)ᵐᵒᵖ` with `hρ`, `automorphismFixedFunctor R p hT K ρ hρ n`
  is the composite of the published `automorphismActionFunctor` of
  `LevelTowerCanonicalCoefficients` with `fixedVectorsActionFunctor`. It sends
  a module sheaf `M` on `X` to the `K`-fixed vectors of the colimit over levels
  of `H^n(T(U), p_U^* M)`, with the action of `Γ`.
  `automorphismHecke R p hT K L g ρ hρ n` is the whiskered
  `heckeActionNatTrans`; its components are the double-coset operators
  (`automorphismHecke_app_hom`), equivariant for `Γ` and natural in `M`.
- For commutative rings `F`, `E` with `Algebra F E` and structure maps
  `s : T ⟶ (Functor.const _).obj (Spec F)`,
  `galoisFixedFunctor R p hT K F E s n` is the composite of the published
  `LevelTowerGalois.galoisCohomologyFunctor F E s p R hT n` with
  `fixedVectorsActionFunctor`. It sends `M` to the `K`-fixed vectors of the
  colimit over levels of `H^n(T(U) ×_{Spec F} Spec E, (p_U ∘ pr₁)^* M)`, with
  the action of `E ≃ₐ[F] E`. `galoisHecke R p hT K L g F E s n` is the
  corresponding natural transformation of double-coset operators
  (`galoisHecke_app_hom`), and `galoisHecke_comm` states that every
  `σ : E ≃ₐ[F] E` commutes with it.

## Towers over levels satisfying a property

Let `P : ObjectProperty (CompactOpenLevel G)` be stable under conjugation
(`IsConjStable P`, from `RestrictedLevelColimit`), and let
`T : P.FullSubcategory ⥤ Scheme.{u}` be a tower over the levels satisfying
`P`, with étale level maps, projections `p` to `X`, and the level-triviality
hypothesis `hT` stated with `restrictedSelfArrow`. Here `K`, `L` are arbitrary
compact open levels, not required to satisfy `P`: the colimit over the
levels satisfying `P` is already a smooth representation of `G`.

- `restrictedAutomorphismFixedFunctor R p hT K ρ hρ n` composes
  `RestrictedLevelTowerCohomology.automorphismActionFunctor` (from
  `RestrictedLevelTowerCanonicalCoefficients`) with
  `fixedVectorsActionFunctor`: it sends `M` to the `K`-fixed vectors of the
  colimit over levels `U` satisfying `P` of `H^n(T(U), p_U^* M)`, with the
  action of `Γ`. `restrictedAutomorphismHecke R p hT K L g ρ hρ n` is the
  whiskered `heckeActionNatTrans`, with components the double-coset
  operators (`restrictedAutomorphismHecke_app_hom`).
- `restrictedGaloisFixedFunctor R p hT K F E s n` composes
  `RestrictedLevelTowerGalois.galoisCohomologyFunctor F E s p R hT n` with
  `fixedVectorsActionFunctor`, for structure maps
  `s : T ⟶ (Functor.const _).obj (Spec F)`. It sends `M` to the `K`-fixed
  vectors of the colimit over levels satisfying `P` of the cohomology of the
  base change to `Spec E`, with the action of `E ≃ₐ[F] E`.
  `restrictedGaloisHecke R p hT K L g F E s n` is the natural transformation
  of double-coset operators (`restrictedGaloisHecke_app_hom`), and
  `restrictedGaloisHecke_comm` states that every `σ : E ≃ₐ[F] E` commutes
  with it.

### Comparison with towers over all levels

Assume in addition that `P` is downward closed (`IsDownwardClosed P`) and
holds for some level (`Nonempty P.FullSubcategory`). Let `T₀` be a tower over
all compact open levels with étale level maps, projections `p₀` and
level-triviality `hT₀`, and restrict it to `P.ι ⋙ T₀` with the published
`restrictProjection P p₀` and `restrict_selfArrow hT₀`.

- Given an action `ρ₀` of `Γ` on `T₀` over `X` and an action `ρ` on the
  restriction over `X` with `hρρ₀ : (ρ γ).unop.hom =
  Functor.whiskerLeft P.ι (ρ₀ γ).unop.hom`,
  `restrictedAutomorphismFixedRestrictIso R p₀ hT₀ K ρ₀ hρ₀ ρ hρ hρρ₀ n` is
  the isomorphism from the restricted `K`-fixed-vector functor to
  `automorphismFixedFunctor R p₀ hT₀ K ρ₀ hρ₀ n`, obtained by whiskering the
  published `automorphismActionRestrictIso` with `fixedVectorsActionFunctor`.
  `restrictedAutomorphismHecke_restrictIso` states that it intertwines
  `restrictedAutomorphismHecke` with `automorphismHecke`.
- For structure maps `s₀` of `T₀` over `Spec F`,
  `restrictedGaloisFixedRestrictIso R p₀ hT₀ K F E s₀ n` is the isomorphism
  from `restrictedGaloisFixedFunctor` of the restricted tower (with structure
  maps `restrictProjection P s₀`) to `galoisFixedFunctor R p₀ hT₀ K F E s₀ n`,
  obtained by whiskering the published
  `RestrictedLevelTowerGalois.galoisCohomologyRestrictIso`.
  `restrictedGaloisHecke_restrictIso` states that it intertwines
  `restrictedGaloisHecke` with `galoisHecke`.

Both intertwining statements are the naturality of `heckeActionNatTrans` at
the component of the published comparison isomorphism.

## Provenance

This is an internal construction from Mathlib's `Functor.mapAction`,
`Action` and natural transformations, the double-coset operators and
fixed-vector functors of `Langlands.Shimura.LevelHecke`, the published
`fixedVectorsMap`, the published `automorphismActionFunctor` and
`LevelTowerGalois.galoisCohomologyFunctor`, and their restricted versions
and comparison isomorphisms in `RestrictedLevelTowerCanonicalCoefficients`
and `RestrictedLevelTowerGalois`. No action, operator, commutation or
comparison is supplied as input. Harris's passages are cited only as
motivation.
