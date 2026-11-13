# Constant locally discrete sheaves for a local action system

Author: Worker 26. The locally discrete analogue of Worker 26's published
`Langlands.Sheaf.Equivariant.LocalActionConstant`, whose `isDiscrete_const` and exactness
instances `constantSheaf_preservesFiniteLimits` and `constantSheaf_preservesFiniteColimits` it
uses. From Worker 26's published `Langlands.Sheaf.Equivariant.LocalActionSmoothPart` it uses
the locally discrete part `smoothPresheaf`, its inclusion `smoothPresheafι`,
`smoothPresheaf_isSheaf`, `map_mem_smoothSubmodule_of_hom`,
`isLocallyDiscrete_iff_forall_mem`, `HasAdmissibleRefinements.covers`, and the instances that
make locally discrete module sheaves abelian with an exact, full and faithful inclusion. From
`Langlands.Sheaf.Equivariant.LocalAction` it uses `IsDiscrete.isLocallyDiscrete`.

All declarations are in `Langlands.Sheaf.Equivariant.LocalActionSystem`.

## Purpose

Harris resolves the constant sheaves `ℤ / ℓ ^ m ℤ`, viewed as étale `G`-sheaves. In the
twisted model the étale `G`-sheaves are the locally discrete sheaves of `LocalActionSmoothPart`
for the distinguished lift system. This module shows that constant sheaves are locally
discrete and that the constant sheaf functor into locally discrete sheaves is exact. It does
this for any local action system with admissible refinements, as `LocalActionConstant` does
for discrete sheaves.

## Data

- A category `T : Type u` with `Category.{v} T`, a topological group `G : Type uG`, a local
  action system `L : LocalActionSystem T G`, a Grothendieck topology `J` on `T`, and
  `[L.HasAdmissibleRefinements J]`.
- A commutative ring `R : Type uR`; presheaves take values in `ModuleCat.{w} R`.

## Declarations

- `smoothPresheafLift L J hP f`: for a locally discrete presheaf `P` (`hP`) and a morphism
  `f : P ⟶ F` of presheaves of modules, the factorization of `f` through the locally discrete
  part `smoothPresheaf L J F`. Each value of `f` is locally discrete because morphisms of
  presheaves preserve locally discrete sections (`map_mem_smoothSubmodule_of_hom`).
  `smoothPresheafLift_comp_ι` (by `rfl`): followed by the inclusion it is `f`.
- `isLocallyDiscrete_sheafify L J hP`, with `[HasWeakSheafify J (ModuleCat R)]`: the
  sheafification of a locally discrete presheaf of modules is locally discrete. The proof
  follows `isDiscrete_sheafify` of `LocalActionConstant`. The locally discrete part of the
  sheafification is a sheaf (`smoothPresheaf_isSheaf`). So the factorization of the canonical
  map `P ⟶ sheafify J P` through it extends, by the universal property of sheafification
  (`sheafifyLift`), to a map `ψ` from the sheafification to its locally discrete part. Then
  `ψ` followed by the inclusion is the identity, because both agree after `toSheafify`
  (`sheafify_hom_ext`). Hence every section of the sheafification is the image of a locally
  discrete section, and so is locally discrete.
- `isLocallyDiscrete_const L J M`: constant presheaves of modules are locally discrete. They
  are discrete (`isDiscrete_const`), and discrete presheaves are locally discrete when
  objects with admissible local actions cover (`IsDiscrete.isLocallyDiscrete` with
  `HasAdmissibleRefinements.covers`).
- `smoothSheafProperty_constantSheaf L J R M`: the constant sheaf of a module is locally
  discrete (the two previous results).
- `smoothConstantSheaf L J R`: the constant sheaf functor
  `ModuleCat R ⥤ L.SmoothSheaf (ModuleCat R) J`, Mathlib's `constantSheaf` lifted to the full
  subcategory. `smoothConstantSheaf_comp_inclusion` (by `rfl`): followed by the inclusion it
  is `constantSheaf J (ModuleCat R)`.
- With `[HasSheafify J (ModuleCat R)]`, the instances
  `smoothConstantSheaf_preservesFiniteLimits` and
  `smoothConstantSheaf_preservesFiniteColimits`: the functor is exact, because its composite
  with the inclusion is the exact constant sheaf functor and the fully faithful inclusion
  reflects finite limits and colimits (Mathlib's
  `preservesFiniteLimits_of_reflects_of_preserves`). `smoothConstantSheaf_additive`: it is
  additive (`Functor.additive_of_preserves_binary_products`).

## Original source and correspondence

Construction infrastructure, with no new source claim. Harris, *Galois properties of
cohomological automorphic forms on GL(n)* (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, §2, printed p.304 = PDF p.6,
Lemma 2.2, resolves the system of constant sheaves `ℤ / ℓ ^ m ℤ` on `U(ẽ)`. The modelling of
étale `G`-sheaves by locally discrete sheaves is recorded in `LocalActionSmoothPart` and
`AnalyticGSheaves`. The proof that the constant sheaf is locally discrete is ours.

## Not formalized here

The comparison of `smoothConstantSheaf` with the discrete `discreteConstantSheaf` of
`LocalActionConstant` when both apply.
