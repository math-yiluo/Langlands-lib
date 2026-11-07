# Simultaneous spreading from a generic cocharacter

This internal construction works in every universe `u`. It uses the published
unconditional dynamic-to-geometric recognition theorem to construct the exact
simultaneous model data from a supplied generic cocharacter presentation and
the explicit generic reductivity spreading premise.

`ReductiveParabolicSpreading.modelDataOfGenericCocharacter` takes a number field
`F : Type u`, an actual connected reductive group `G`, a closed subgroup
homomorphism `p : P ⟶ G`, and an actual cocharacter `χ` with
`SubgroupFunctor.range p = Dynamic.parabolic χ`. This equality is equality of
subgroup functors on every test scheme. Its other substantive input is the
published proposition `GenericReductivitySpreadingStatement.{u}`.
The constructor returns a dependent pair of a finite set `S` of finite places
and the exact published `ReductiveParabolicSpreading.ModelData R F p`, where
`R = (S : Set (FinitePlace F)).integer F`. All field, algebra and fraction-ring
structures are the canonical structures of this actual S-integer subalgebra.
There is no splitness, rank, anisotropy or proper-parabolic restriction.

## Field parabolicity from recognition

Let `R` be a Noetherian domain with supplied fraction field `K`, and let
`M : IntegralModel R K G` have smooth structural map. Fix a closed subgroup
`p : P ⟶ G` and an integral cocharacter `χ : Gm(Spec R) ⟶ M.group` with the
published generic presentation

```text
range (p ≫ M.genericIso.inv)
  = Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ).
```

`DynamicParabolic.fieldParabolic_of_connectedReductive` concerns the actual
model and inclusion already constructed by `DynamicParabolic.model` and
`DynamicParabolic.inclusion`. For every `k : Type u`, every field structure and
every `Algebra R k`, it assumes connected reductivity of the ambient pullback
along the actual `Spec.algebraMap R k`. Closedness of the same dynamic
inclusion is stable under this base change.
`Dynamic.Affine.isRepresentedBy_parabolicHom_baseChange` identifies its range
with the dynamic subgroup of the changed cocharacter. The published
`isParabolicSubgroup_of_range_eq_dynamicParabolic` then proves
`IsParabolicSubgroup` for this changed inclusion. Thus this clause uses no
parabolic classification premise.

`DynamicParabolic.modelDataOfCocharacter` assembles the exact `ModelData R K p`
from the supplied ambient model, its integral `IsReductive` certificate and
connected reductivity at every field algebra. It reuses the existing dynamic
model, its actual generic isomorphism and compatible inclusion, closedness,
smoothness and connected-fibre proof. Its field-parabolic clause is the
recognition argument above. In particular, the generic comparison and all
fibre conclusions refer to the same model and homomorphism.

## Arithmetic extension and generic comparison

`modelDataOfGenericCocharacter` first uses
`ArithmeticSpreading.reductiveModelData` under the explicit generic spreading
premise. It then applies `enlargedCocharacterData` to the supplied generic
cocharacter. This constructs a finite enlargement of the arithmetic place set
and an actual integral cocharacter whose generic fibre recovers that same `χ`
through the enlarged model's prescribed `genericIso`.

`fieldReductive_enlargeModel` supplies connected reductivity of every field
fibre of the enlarged model. `isReductive_of_fieldReductive` proves its integral
`IsReductive` predicate; `smooth_enlargeModel` and
`adelicSIntegersNoetherian` supply smoothness and Noetherianity for the dynamic
construction.

Closedness and the supplied range equality make `p` a representative of the
generic dynamic subgroup. Transport through the inverse of the enlarged
model's generic isomorphism, together with
`Dynamic.parabolic_eq_comap_of_iso` and the exact cocharacter recovery equation,
gives the required range equality in that enlarged generic fibre. The preceding
`modelDataOfCocharacter` constructor then fills every field of `ModelData`.
Its inclusion extends exactly the supplied `p` with the published
`IntegralModel.Hom.generic_comm` equality.

## Provenance and remaining obligations

The provenance is internal derived content from the imported, published
arithmetic spreading, cocharacter extension, represented-subgroup transport,
dynamic model construction and arbitrary-field recognition APIs. The generic
comparison follows the existing conditional simultaneous-spreading assembly,
with the generic cocharacter now an explicit input and field parabolicity
proved by recognition.

This module does not prove `GenericReductivitySpreadingStatement`, choose a
cocharacter for an arbitrary geometrically parabolic subgroup, or prove the
unconditional `ReductiveParabolicSpreading.ExistenceStatement`. The forward
cocharacter construction and generic reductivity spreading remain substantive
obligations. The existing conditional assembly and the exact target's
Lean/Markdown pair and import closure are unchanged.
