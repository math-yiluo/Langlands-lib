# Constant discrete sheaves for a local action system

Author: Worker 26. Builds on `Langlands.Sheaf.Equivariant.LocalActionDiscretePart`
(Worker 26), which gives the discrete part `discretePresheaf L F` of a presheaf of modules,
its inclusion `discretePresheafι L F`, the fact that it is a sheaf when `F` is
(`discretePresheaf_isSheaf`, under `L.HasFiniteEquivariantRefinements J`), and the abelian
category `L.DiscreteSheaf (ModuleCat.{w} R) J` of discrete sheaves with its exact inclusion
`L.discreteSheafInclusion`. Through it, the module uses Worker 13's local action systems
(`Langlands.Sheaf.Equivariant.LocalAction`). From Mathlib it uses the constant sheaf functor
`constantSheaf J A` (`Mathlib.CategoryTheory.Sites.ConstantSheaf`), sheafification with its
universal property (`sheafifyLift`, `toSheafify_sheafifyLift`, `sheafify_hom_ext`) and full
subcategories (`ObjectProperty.lift`).

All declarations are in the namespace `Langlands.Sheaf.Equivariant`.

## Setting

`T` is a category with a Grothendieck topology `J`, `G` a group with a topology, and
`L : LocalActionSystem T G` a local action system. `R : Type uR` is a commutative ring,
and module presheaves take values in `ModuleCat.{w} R`.

## Purpose

Harris resolves the constant sheaves `ℤ/ℓ^mℤ` (Lemma 2.2), viewed as sheaves in smooth
modules, that is, as discrete sheaves in Berkovich's sense. The published divisible
system modules for discrete sheaves take an arbitrary `ℓ`-divisible system as input. This
module supplies the constant sheaves as discrete sheaves and proves that the constant
sheaf functor into discrete sheaves is exact, so that it carries `ℓ`-divisible systems of
modules to `ℓ`-divisible systems of discrete sheaves (see
`Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtaleConstant`).

## Discreteness of constant presheaves and of sheafifications

- `isDiscrete_const L M`: the constant presheaf `(Functor.const Tᵒᵖ).obj M` is discrete.
  Every arrow acts on its sections by the identity, so every admissible local action fixes
  every section on its whole domain subgroup.
- `discretePresheafLift L hP f`: a morphism `f : P ⟶ F` from a discrete presheaf `P`
  factors through the discrete part of `F`, because morphisms of presheaves preserve
  discrete sections (`map_mem_discreteSubmodule_of_hom`). `discretePresheafLift_comp_ι`
  states the factorization; it holds by `rfl`.
- `isDiscrete_sheafify hP`: with `[HasWeakSheafify J (ModuleCat.{w} R)]` and
  `[L.HasFiniteEquivariantRefinements J]`, the sheafification `sheafify J P` of a discrete
  presheaf `P` is discrete.

  Proof. The canonical map `toSheafify J P` factors through the discrete part of
  `sheafify J P` (`discretePresheafLift`). That discrete part is a sheaf
  (`discretePresheaf_isSheaf`), so the universal property of sheafification
  (`sheafifyLift`) gives a map `ψ` from `sheafify J P` to its discrete part. The composite
  of `ψ` with the inclusion `discretePresheafι` agrees with the identity after composing
  with `toSheafify J P` (`toSheafify_sheafifyLift`), hence equals the identity
  (`sheafify_hom_ext`). So every section `s` of `sheafify J P` is the image of the
  discrete section `ψ s`, and is discrete (`isDiscrete_iff_forall_mem`). The proof does
  not use the local surjectivity of the map to the sheafification.

## The constant sheaf functor into discrete sheaves

In this section `[HasWeakSheafify J (ModuleCat.{w} R)]` and
`[L.HasFiniteEquivariantRefinements J]`.

- `discreteSheafProperty_constantSheaf L J R M`: the constant sheaf
  `(constantSheaf J (ModuleCat.{w} R)).obj M` is discrete, by `isDiscrete_const` and
  `isDiscrete_sheafify`.
- `discreteConstantSheaf L J R : ModuleCat.{w} R ⥤ L.DiscreteSheaf (ModuleCat.{w} R) J`:
  Mathlib's constant sheaf functor, with values in discrete sheaves
  (`ObjectProperty.lift`).
- `discreteConstantSheaf_comp_inclusion L J R`: followed by the inclusion into all sheaves
  it is `constantSheaf J (ModuleCat.{w} R)`. This holds by `rfl`.

## Exactness

In this section `[HasSheafify J (ModuleCat.{w} R)]` and
`[L.HasFiniteEquivariantRefinements J]`. All five declarations are instances.

- `constantSheaf_preservesFiniteLimits`, `constantSheaf_preservesFiniteColimits`: the
  constant sheaf functor preserves finite limits and finite colimits. It is the composite
  of the constant presheaf functor with sheafification
  (`Functor.const Tᵒᵖ ⋙ presheafToSheaf J _`), and Mathlib provides both properties for
  that composite.
- `discreteConstantSheaf_preservesFiniteLimits`,
  `discreteConstantSheaf_preservesFiniteColimits`: the same for `discreteConstantSheaf`.
  The composite with the fully faithful inclusion `L.discreteSheafInclusion` is the
  constant sheaf functor, and a fully faithful functor reflects finite limits and finite
  colimits (`preservesFiniteLimits_of_reflects_of_preserves` and its colimit version).
- `discreteConstantSheaf_additive`: `discreteConstantSheaf` is additive, since it
  preserves binary products (`Functor.additive_of_preserves_binary_products`).

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39 (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, printed p.304 = PDF p.6
(checked with `pdftotext` for this module):

- "Here `T` is an 'étale sheaf in smooth `ℤ/ℓ^mℤ[S(ẽ)]`-modules' if, for any quasi-étale
  morphism `U → U(ẽ)` with `U` compact the action of the stabilizer `S(ẽ)_U ⊂ S(ẽ)` on
  `T(U)` is smooth; in other words, `T` is what Berkovich calls discrete."
- "Lemma 2.2. For each `m` the constant sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic resolution
  `0 → ℤ/ℓ^mℤ → F_m^0 → F_m^1 → ⋯` such that, for each `q`, `{F_m^q}` is an `ℓ`-divisible
  system of `S(ẽ)`-modules over `U(ẽ)`."

## Provenance

Harris uses, without comment, that the constant sheaves are sheaves in smooth modules and
that they form an `ℓ`-divisible system. In the local action system framework, these facts
become the discreteness of the sheafified constant presheaf and the exactness of the
constant sheaf functor into discrete sheaves. Both statements and their proofs are ours.
They hold for an arbitrary local action system with finite equivariant refinements,
because the discrete part of a sheaf is then a sheaf. The site, the local action system
and the comparison with Harris's étale sheaves on `U(ẽ)` are not part of this module.
