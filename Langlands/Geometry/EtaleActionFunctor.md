# Cohomology functors on equivariant étale coefficients

This internal specialization adds functoriality in equivariant coefficient
morphisms to `EtaleActionDiagram`. The inputs remain an actual scheme
`Y : Scheme.{u}`, a commutative ring `R : Type u`, a group `G : Type w`,
and `ρ : G →* (Aut Y)ᵐᵒᵖ`. Coefficients are actual small-étale sheaves of
`ModuleCat.{u} R`, with the existing translation-equivariant structure.
There is no topology on `G`.

The category on `EquivariantSheaf R ρ` is the category constructed in
`TranslationEquivariantCategory`. A morphism `f : F ⟶ E` is a sheaf
morphism `f.hom` satisfying

```text
F.act g ≫ f.hom = (translate by g).map f.hom ≫ E.act g.
```

`ofEquivariantFunctor` extends the existing conversion to compatible
coefficients on `actionSchemeDiagram ρ`. On the single vertex, its map
is `f.hom`; its diagram commutation condition is exactly the displayed
equivariance equation. The functor is faithful because evaluation at that
vertex recovers the entire underlying morphism.

For every `q : ℕ`, `pullbackCohomologyMap f q` is a morphism between the
previously constructed geometric pullback actions on ordinary degree-`q`
cohomology. Its underlying map is precisely

```text
(EtaleDerivedSections.cohomology Y R q).map f.hom.
```

The proof of equivariance uses naturality of the compatible-coefficient
cohomology diagram and the existing equality of each diagram arrow with
the geometric pullback action. In particular, no commutation equation on
cohomology is an input. These maps form `pullbackCohomologyFunctor R ρ q`;
its identity and composition laws follow from those of right-derived
cohomology. `pullbackCohomologyFunctor_map_hom` records the exact formula.

`ofEquivariantCohomologyFunctorIso` promotes the earlier objectwise
comparison to a natural isomorphism in coefficient sheaves. Its components
are `ofEquivariantCohomologyIso`, hence identity maps on the underlying
cohomology modules. Naturality in a coefficient morphism reduces to the
identity composition laws for the same usual cohomology map.

`pullbackSectionsFunctor` composes compatible-coefficient sections with
Mathlib's equivalence from single-object diagrams to actions. Its underlying
module is ordinary global sections. The underlying map on coefficients is
ordinary sections of `f.hom`, as proved by `pullbackSectionsFunctor_map_hom`.
For `σ_g = aut ρ g`, `pullbackSectionsFunctor_obj_ρ` proves that `g` acts by

```text
(sectionsMap σ_g.hom R).app F.obj
  ≫ (EtaleDerivedSections.sections Y R).map (F.act g).
```

Finally, `pullbackCohomologyZeroFunctorIso` identifies degree-zero
cohomology with this section-action functor. It first uses the unit of the
action/diagram equivalence, then the inverse cohomology-diagram comparison,
then the compatible-coefficient degree-zero comparison, all whiskered by
the appropriate functors. It is therefore an isomorphism of functors into
`Action (ModuleCat R) G`, natural in coefficients and equivariant for every
group element.
The final lemma `pullbackCohomologyZeroFunctorIso_hom_app_hom` identifies
each underlying forward component with the existing canonical
`EtaleDerivedSections.cohomologyZeroIso` component. This follows because
the preceding two comparison factors have identity underlying maps.

The provenance is internal: the file combines the actual category from
`TranslationEquivariantCategory`, the action and coefficient conversion
from `EtaleActionDiagram`, and the natural cohomology/section constructions
from `EtaleCohomologyDiagramFunctor`. No new original-literature theorem is
asserted. The scalar ring, scheme and group action stay fixed. This does
not assert smoothness, continuity, compact supports, derived functors in
the equivariant category, coefficient-ring change, inverse-limit
comparisons, or realization of a Harris level scheme.
