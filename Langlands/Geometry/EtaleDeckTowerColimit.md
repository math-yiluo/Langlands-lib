# Level colimits of canonical deck-tower cohomology and their smoothness

This internal construction passes the existing canonical cohomology of an
actual over-base deck tower to the colimit over its levels. It constructs the
level inclusions, records their compatibilities, and proves that the colimit
is a smooth representation whenever an open subgroup acts by the identity on
the original geometry of each level. Two general statements about colimits
of module actions, in namespace `Langlands`, support it. All other new
declarations are in `Langlands.Geometry.EtaleCanonicalDeckTower`.

## Motivation and scope

Harris writes the cohomology of a Shimura variety as the colimit over levels
of finite-level cohomology, with a smooth group action. This module supplies
the corresponding colimit construction for the existing canonical deck
towers. A single group `G` acts at every level through actual over-base
automorphisms; for instance, a compact group can act on its normal sublevels
through finite quotients. Hecke operators or a full adelic group action
moving between levels are not constructed. Nor does this module form a
derived colimit, identify a tower with a Shimura tower, or assert an analytic,
compact-support or arithmetic comparison. Those remain separate obligations of
the broader Harris task.

## General colimits of module actions

Let `R : Type u` be a commutative ring, `G : Type t` a group, and
`D : K ⥤ Action (ModuleCat.{u} R) G` a diagram over any category
`K : Type v` with `Category.{w} K` and `HasColimitsOfShape K (ModuleCat.{u} R)`.
`Rep.ActionToRep R G` is the existing functor presenting a module action as a
representation.

With a topology on `G`:

- `isSmooth_actionToRep_of_open_trivial` states that a module action `V` is
  smooth (`Langlands.IsSmooth`) when one open subgroup `U` satisfies
  `V.ρ g = 𝟙 V.V` for every `g ∈ U`. Every vector is then fixed by `U`.
- `isSmooth_actionToRep_colimit` states that `colimit D` is smooth when each
  vertex `D.obj i` has such an open subgroup, which may depend on `i`.
  No filteredness of `K` is assumed.

The proof of the colimit statement is as follows. Let `S` be the existing
submodule `smoothVectors` of the colimit representation. The image of each
colimit inclusion lies in `S`, because the inclusion is equivariant and the
chosen open subgroup acts trivially on its source. The forgetful functor
`Action.forget` preserves the colimit, so the underlying cocone is a colimit
of modules. The quotient map `S.mkQ` vanishes on every inclusion, and
uniqueness of maps out of that colimit gives `S.mkQ = 0`. Hence
`S = ker S.mkQ = ⊤`, and every vector is smooth.

Without a topology, `actionColimit_exists_rep` additionally assumes
`PreservesColimitsOfShape K (forget (ModuleCat.{u} R))`. It states that every
vector `x` of `(colimit D).V` has the form `(colimit.ι D i).hom.hom y` for
some vertex `i` and some `y` in `(D.obj i).V`. The proof applies Mathlib's
`Concrete.isColimit_exists_rep` to the underlying colimit of modules. For a
small filtered `K : Type u`, Mathlib's instances provide both this
preservation hypothesis and `HasColimitsOfShape K (ModuleCat.{u} R)`.

## Inputs from the canonical deck tower

Let `X : Scheme.{u}`, `J : Type v` with `Category.{w} J`, `G : Type t` a
group, `R : Type u` a commutative ring and

```lean
A : J ⥤ Action ((Over X)ᵒᵖ) G
```

the original geometric tower. `cohomologyFunctor R A q` and
`sectionsFunctor R A` are the existing functors from `ModuleSheaf X R` to
`J ⥤ Action (ModuleCat.{u} R) G`. Their level-`i` objects are ordinary
étale cohomology and global sections of the canonical pullback of a base
sheaf `M` to the level scheme. Their group action is pullback with
coefficients along the original deck map `((A.obj i).ρ g).unop.left`, and
their transition maps are pullback along the original level maps.
`cohomologyZeroFunctorIso R A` is the existing degree-zero recovery.

All cohomological declarations retain the existing ambient choices

```lean
[∀ x : J × SingleObj G,
  HasDerivedCategory.{wS} (ModuleSheaf ((schemeDiagram A).obj x).unop R)]
[HasDerivedCategory.{wR} (ModuleCat.{u} R)]
```

These choices are needed only to define the existing level functors. A local
instance, copied from the parent module, presents the first family at each
level scheme `(A.obj i).V.unop.left`. The derived-category universes `wS`
and `wR` are independent. Schemes, coefficients and modules share universe
`u`. The level and group universes are independent.

## Dependence of the level action on the original geometry

The following two theorems hold for every group element and require neither
colimits nor a topology:

- `cohomologyFunctor_obj_obj_ρ_congr` and `sectionsFunctor_obj_obj_ρ_congr`
  state that if `(A.obj i).ρ g = (A.obj i).ρ h`, then the level-`i`
  cohomology or section actions of `g` and `h` coincide. The proof rewrites
  both sides with the existing action formula. It then uses that pullback
  with coefficients along an over-base map, together with its canonical
  coefficient isomorphism, depends only on the original geometric arrow.
- `cohomologyFunctor_obj_obj_ρ_eq_id` and `sectionsFunctor_obj_obj_ρ_eq_id`
  state that `(A.obj i).ρ g = 𝟙 _` implies that `g` acts by the identity on
  level-`i` cohomology or sections. The proof compares `g` with `1` by the
  congruence theorem and applies the action's unit law.

## Colimit functors and level inclusions

With `[HasColimitsOfShape J (ModuleCat.{u} R)]`, Mathlib provides the
corresponding colimits of module actions. The constructions are:

| Declaration | Definition |
| --- | --- |
| `colimitCohomologyFunctor R A q` | `cohomologyFunctor R A q ⋙ colim` |
| `colimitSectionsFunctor R A` | `sectionsFunctor R A ⋙ colim` |
| `colimitCohomologyZeroIso R A` | whiskering of `cohomologyZeroFunctorIso R A` by `colim` |
| `levelCohomologyι R A q i` | the natural transformation with components `colimit.ι _ i` |
| `levelSectionsι R A i` | the natural transformation with components `colimit.ι _ i` |

Both colimit functors take values in `Action (ModuleCat.{u} R) G`. They are
functorial in every base sheaf morphism. The level inclusions have source
the level-`i` evaluation of the corresponding level functor. Each component
is a morphism of actions, hence `G`-equivariant. Naturality follows from
`ι_colimMap`.

The following statements hold:

- `levelCohomologyι_app` and `levelSectionsι_app` expose the components
  `colimit.ι` by reflexivity.
- `levelCohomologyι_w` and `levelSectionsι_w` state that, for every level
  arrow `a : i ⟶ j`, the level-`j` inclusion precomposed with the whiskered
  level transition equals the level-`i` inclusion. This is `colimit.w`.
- `levelCohomologyι_zero` states that the level-`i` degree-zero inclusion
  followed by `colimitCohomologyZeroIso` equals the levelwise degree-zero
  recovery followed by the level-`i` section inclusion. The proof uses
  `ι_colimMap`.
- `levelCohomologyι_comm` and `levelSectionsι_comm` record the equivariance
  equation `ρ_i(g) ≫ ι_i = ι_i ≫ ρ(g)` for the colimit action.

## Underlying modules

`colimitCohomologyForgetIso R A q` and `colimitSectionsForgetIso R A` are
natural isomorphisms in the base sheaf. They identify the underlying module of
the colimit with the colimit of the underlying level modules. Each is the
associator followed by Mathlib's `preservesColimitNatIso` for
`Action.forget (ModuleCat.{u} R) G`, whiskered by the level functor.
`levelCohomologyι_colimitCohomologyForgetIso` and
`levelSectionsι_colimitSectionsForgetIso` state that this isomorphism
carries the underlying map of each level inclusion to the corresponding
colimit inclusion of modules. Their proof uses `ι_preservesColimitIso_hom`.

With the additional hypothesis
`PreservesColimitsOfShape J (forget (ModuleCat.{u} R))`,
`levelCohomologyι_exists_rep` and `levelSectionsι_exists_rep` state that
every vector of the colimit cohomology or sections is the image of some vector
at some level under the corresponding level inclusion. They specialize
`actionColimit_exists_rep`.

## Smoothness

Assume `[TopologicalSpace G]`. The definition `IsLevelwiseSmooth A` is the
proposition

```lean
∀ i : J, ∃ U : OpenSubgroup G, ∀ g ∈ U, (A.obj i).ρ g = 𝟙 (A.obj i).V
```

It is a hypothesis on the original geometry alone; no cohomological action is
assumed smooth. Here `(A.obj i).ρ g` is the over-base automorphism in
`(Over X)ᵒᵖ`.

For a levelwise smooth tower:

- `isSmooth_levelCohomology` and `isSmooth_levelSections` state that every
  level of ordinary cohomology or sections is smooth. They do not need level
  colimits. The proof combines `..._ρ_eq_id` with
  `isSmooth_actionToRep_of_open_trivial`.
- `isSmooth_colimitCohomology` and `isSmooth_colimitSections` state that the
  colimit cohomology and colimit sections are smooth. The proof applies
  `isSmooth_actionToRep_colimit` with the same open subgroup at each level.

These statements give functors to the existing category
`SmoothRep.{u, t, u} R G` of smooth representations, obtained from
`(smoothRepProperty R G).lift`:

- `smoothLevelCohomologyFunctor R A hA q i` and
  `smoothLevelSectionsFunctor R A hA i`, lifting the level-`i` functors
  composed with `Rep.ActionToRep R G`;
- `smoothColimitCohomologyFunctor R A hA q` and
  `smoothColimitSectionsFunctor R A hA`, lifting the colimit functors composed
  with `Rep.ActionToRep R G`.

`smoothColimitCohomologyFunctor_obj_obj` and
`smoothColimitSectionsFunctor_obj_obj` identify the underlying representation
by reflexivity.

`smoothLevelCohomologyι` and `smoothLevelSectionsι` are the level inclusions
as natural transformations of functors to smooth representations. Their
components are `Rep.ActionToRep R G` applied to the components of
`levelCohomologyι` and `levelSectionsι`. Naturality follows from the original
naturality after functoriality of `Rep.ActionToRep R G`.
`smoothLevelCohomologyι_app_hom` and `smoothLevelSectionsι_app_hom` record
these components.

`smoothColimitCohomologyZeroIso R A hA` is the natural isomorphism from
degree-zero smooth colimit cohomology to smooth colimit sections. Its
components are `Rep.ActionToRep R G` applied to the components of
`colimitCohomologyZeroIso`, and its naturality is transported in the same way.
`smoothColimitCohomologyZeroIso_hom_app_hom` records its forward component.

## Provenance

This is internal construction. The colimits, their preservation by forgetful
functors, the lift to a full subcategory and the representative lemma are
Mathlib. The level functors, action formulas, degree-zero recovery,
smoothness predicates and smooth-representation category are existing
Library constructions. The proofs above derive every action and smoothness
property from the original geometry. No cohomology groups, actions,
smoothness of a cohomological action or level-compatibility equations are
supplied as input data.
