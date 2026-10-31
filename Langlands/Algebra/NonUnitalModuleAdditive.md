# Pointwise additive structure on original nonunital modules

Worker 633. This is an internal derived construction over the published original
additive nonunital actions, their intertwiners and their integer-unitization
categorical equivalence. Its structures and intrinsic laws implement pointwise
addition and finite products without assuming a unit law for the original action.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant original passages were read at printed pages 5–7 / PDF pages 11–13,
A.VI.1 printed page 261 / PDF page 267, and A.VI.2 property 6 printed page 262 /
PDF page 268. The supplementary 2010 errata, registered as
`renard-2010-corrections-complements`, were read at PDF pages 18–19, together
with the current Library note `notes/renard/appendix-a-corrections.md`.
The [author's book and errata section](https://perso.pages.math.cnrs.fr/users/david.renard/)
was checked live on 30 October 2026: the page is byte-identical to the registered
`renard-author-page-2026-10-26` snapshot, and the linked 2010 errata retain their
registered fingerprint. That book section links the corrected 2026 French
edition and the separate 2010 errata; it has no separate 2026 errata link.

The source conventions allow rings without a unit and actions without a unit
law even over unital rings. I.1.2 introduces the separate nondegenerate
subcategory. A.VI.1 explicitly requires finite products among the abelian
category axioms; A.VI.2 property 6 describes abelian Hom groups and distributive
composition. The explicit Lean structures here, and the transport through integer
unitization, are internal derived content motivated by those passages. They are
not the source's complex-linear scalar construction and do not prove the later
abelianness assertions. In particular the unsupported full-subcategory closure
claim identified in the correction note is not used.

## Hom groups and composition

For `A : Type u`, `M : Type v`, and `N : Type w`, with `[NonUnitalRing A]`,
the given additive groups and the original `[NonUnitalModule A M]` and
`[NonUnitalModule A N]`, the new instances `NonUnitalModuleHom.instZero`,
`instAdd`, and `instNeg` use the zero, sum and negative of the given underlying
`AddMonoidHom`. The intertwining equations follow from `smul_zero`,
`smul_add`, and `smul_neg`, respectively. The evaluation laws `zero_apply`,
`add_apply` and `neg_apply`, and the forgetful equalities
`toAddMonoidHom_zero`, `toAddMonoidHom_add` and `toAddMonoidHom_neg`, are
definitional. `instAddCommGroup` proves the group laws by evaluation in the
codomain; natural and integer scalar multiplication use the standard group
recursors. `toAddMonoidHomAddHom` bundles the underlying-map operation as an
additive homomorphism.

The original `id` and `comp` are unchanged. `comp_add` uses additivity of the
postcomposed map. `add_comp` holds by evaluation. The named instance
`NonUnitalModuleCat.preadditive` uses this exact unbundled Hom group and these
two composition laws. `homGroup_eq` records definitional agreement, avoiding an
additional transported Hom group. Thus the category's standard
`Preadditive.add_comp` and `Preadditive.comp_add` apply to the original composition.

## Existing unitization functors and finite products

All objects, maps, functors and equivalence data in
`Langlands.Algebra.IntegerUnitizationCategory` are reused unchanged. The lemmas
`IntegerUnitization.extendMap_toAddMonoidHom` and
`restrictMap_toAddMonoidHom` retain their entire underlying additive maps.
`extendMap_zero`, `extendMap_add`, `extendMap_neg`, `restrictMap_zero`,
`restrictMap_add` and `restrictMap_neg` prove compatibility by evaluation.
The named instances `extendFunctor_additive` and `restrictFunctor_additive`
make the existing functors additive between the pointwise structure and the
usual `ModuleCat` preadditive structure. The standard functor map-zero,
map-addition and map-negation interfaces therefore also apply.

`NonUnitalModuleCat.hasFiniteProducts` supplies an actual `HasFiniteProducts`
instance. For each `n`, it transports a `Discrete (Fin n)` limit from
`ModuleCat (Unitization ℤ A)` using
`Adjunction.hasLimitsOfShape_of_equivalence` and the existing
`IntegerUnitization.extendFunctor_isEquivalence`. The target limit structure is
Mathlib's ordinary module-category structure; no source limit structure is an
input. The case `n = 0` is included. This unit does not choose explicit product
carriers or projection formulas.

## Size, verification and scope

The Hom construction keeps the scalar, source and target universes independent.
The category constructions have the full types

```lean
(A : Type u) → [NonUnitalRing A] →
  Preadditive (NonUnitalModuleCat.{u, v} A)

(A : Type u) → [NonUnitalRing A] →
  HasFiniteProducts (NonUnitalModuleCat.{u, v} A)
```

The additive functor interfaces similarly quantify over arbitrary `A : Type u`
with `[NonUnitalRing A]`, and return respectively
`(IntegerUnitization.extendFunctor.{u, v} A).Additive` and
`(IntegerUnitization.restrictFunctor.{u, v} A).Additive`.
The module checks complete unapplied types, specialization to `(u,v) = (0,1)`
and `(1,0)`, and downstream instance inference. No same-universe restriction or
replacement of `Type v` carriers by `Type (max u v)` is introduced.

Zero rings, zero carriers, and zero original actions are included. No
idempotentedness, nondegeneracy, scalar field, nontriviality, finite generation
or finite dimension is assumed. Ambient abelianness, concrete kernels/cokernels,
nondegenerate closure or abelianness, exactness, recovered scalar Hom spaces,
complex categorical comparisons, tensor products and adjunctions remain separate
obligations.
