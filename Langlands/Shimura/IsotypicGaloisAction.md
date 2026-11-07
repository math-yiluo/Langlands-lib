# Isotypic parts and multiplicity spaces with a commuting group action

This internal construction applies the isotypic part and the multiplicity
space for a representation `τ` to smooth representations that carry a
commuting action of a second group `Γ`. Such representations are the objects
of Mathlib's `Action (SmoothRep R G) Γ`. The isotypic part keeps the
restricted actions of both groups. The multiplicity space `Hom_G(τ, -)` is a
representation of `Γ`, acting by composition. Both constructions are
functorial. The evaluation map `τ ⊗ Hom_G(τ, V) → V[τ]` is surjective and
equivariant for both groups. All declarations are in namespace
`Langlands.Shimura.IsotypicGaloisAction`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, printed p. 312, writes `H^{n-1}(S_K(N), W)[π]` for the
`JL(π_f)`-isotypic component of the cohomology of a Shimura variety. This
component carries the action of a Galois group commuting with
`GG(A_f)`. Formulas (5.2), (5.3) and (5.5) on printed pp. 312-313 use
spaces of intertwining maps of representations, and Theorem 5.7 on printed
p. 313 describes the Galois representations on these components. The
published cohomology functors in the Library take values in
`Action (SmoothRep R G) Γ`. This module provides the isotypic parts and
multiplicity spaces of such objects with their `Γ`-actions, for an
arbitrary representation `τ`.

`τ` is any `R`-linear representation of `G`. No irreducibility,
admissibility or smoothness of `τ` is assumed, and nothing is proved about
the structure of the isotypic part beyond the surjectivity of evaluation.
No topology on `Γ` and no continuity of its action is considered. No
statement of Harris is formalized.

## Inputs

Let `R : Type uR` be a commutative ring, `G : Type uG` a group with a
topology, `U : Type uU` an `R`-module and `τ : Representation R G U`. Let
`Γ : Type uΓ` be a group.

The published module `Langlands.Cohomology.HyperextDegenerationIsotypic`
provides, in namespace `Langlands.Cohomology.HyperextAbutment`, the
`τ`-isotypic part `isotypicPart τ ρ` of a representation `ρ`: the supremum
of the ranges of all intertwining maps `τ → ρ`. It also provides the
subrepresentation `isotypicSubrepresentation τ ρ` on it, and the lemmas
`apply_mem_isotypicPart`, `isotypicPart_le_iff` and
`intertwiningMap_apply_mem_isotypicPart`. The published module
`Langlands.Representation.Category.Subquotients` provides the smooth
representation `SmoothRep.subrepresentation A S` on an invariant submodule,
its inclusion `SmoothRep.subtype A S` and `SmoothRep.subtype_injective`.
Mathlib provides `Action V Γ`, `Functor.mapAction`, `Rep.ActionToRep`,
`Representation.IntertwiningMap` with `llcomp`, and `TensorProduct.lift`.

## The underlying representation of the second group

For `X : Action (SmoothRep R G) Γ`:

- `galoisRepresentation X : Representation R Γ X.V`: `γ` acts by the
  underlying linear map of `X.ρ γ` (`galoisRepresentation_apply`, by
  `rfl`).
- `galoisRepresentation_commutes`: the action of every `γ : Γ` commutes with
  the action of every `g : G`, since `X.ρ γ` is an intertwining map.
- `galoisRepresentation_naturality`: a morphism `f : X ⟶ Y` intertwines
  `galoisRepresentation X` and `galoisRepresentation Y`.

## Isotypic parts

For a smooth representation `A` of `G`:

- `isotypicObj τ A` is the smooth representation
  `SmoothRep.subrepresentation A (isotypicSubrepresentation τ A.representation)`,
  the restriction of `A` to its `τ`-isotypic part.
- `isotypicMap τ f : isotypicObj τ A ⟶ isotypicObj τ B` is the restriction
  of a morphism `f : A ⟶ B`, using
  `intertwiningMap_apply_mem_isotypicPart`. `coe_isotypicMap_apply` states
  that on underlying elements it is `f`, by `rfl`.
- `isotypicFunctor τ` is the functor on `SmoothRep R G` with these objects
  and maps (`isotypicFunctor_obj`).
- `isotypicι τ : isotypicFunctor τ ⟶ 𝟭 _` is the natural inclusion, with
  components `SmoothRep.subtype`. `isotypicι_app_apply` states that it sends
  `x` to `x.1`, `isotypicι_app_injective` that its components are
  injective, and an instance that they are monomorphisms.
- `isotypicActionFunctor τ Γ` is `Functor.mapAction Γ` of
  `isotypicFunctor τ`, an endofunctor of `Action (SmoothRep R G) Γ`.
  `isotypicActionFunctor_obj_V` and `isotypicActionFunctor_obj_ρ` state by
  `rfl` that the underlying smooth representation is `isotypicObj τ X.V`
  and that `γ` acts by `isotypicMap τ (X.ρ γ)`.
- `isotypicActionι τ Γ : isotypicActionFunctor τ Γ ⟶ 𝟭 _` is the inclusion,
  equivariant for both groups and natural (`isotypicActionι_app_hom`).
- `isotypicGaloisRepresentation τ Γ X` is the representation of `Γ` on
  `isotypicPart τ X.V.representation`, the `galoisRepresentation` of
  `(isotypicActionFunctor τ Γ).obj X`.
  `coe_isotypicGaloisRepresentation_apply` states that it is the restriction
  of `galoisRepresentation X`, by `rfl`.

## Multiplicity spaces

- `multiplicityFunctor τ : SmoothRep R G ⥤ ModuleCat R` sends `A` to the
  `R`-module `τ.IntertwiningMap A.representation` of intertwining maps, and
  a morphism to composition with it (`multiplicityFunctor_map_apply`). The
  values lie in `ModuleCat.{max uU uV} R`.
- `multiplicityActionFunctor τ Γ` is `Functor.mapAction Γ` of
  `multiplicityFunctor τ`, with values in `Action (ModuleCat R) Γ`.
- `multiplicityRepFunctor τ Γ` is `multiplicityActionFunctor τ Γ` followed
  by Mathlib's `Rep.ActionToRep R Γ`, with values in `Rep R Γ`.
- `multiplicityRepresentation τ Γ X` is the representation of `Γ` on
  `τ.IntertwiningMap X.V.representation` of
  `(multiplicityRepFunctor τ Γ).obj X`. `multiplicityRepresentation_apply`
  states that `γ` sends `φ` to `(SmoothRep.hom (X.ρ γ)).comp φ`, by `rfl`.

## The evaluation map

- `isotypicEvaluation τ A :
  U ⊗[R] τ.IntertwiningMap A.representation →ₗ[R] isotypicPart τ A.representation`
  is the linear map with `u ⊗ φ ↦ φ u`, defined by `TensorProduct.lift`
  and `apply_mem_isotypicPart` (`coe_isotypicEvaluation_tmul`).
- `isotypicEvaluation_surjective`: it is surjective. By
  `isotypicPart_le_iff`, the isotypic part lies in the image of its range,
  since every `φ u` is the value at `u ⊗ φ`.
- `isotypicEvaluation_map_tmul`: on pure tensors, evaluation intertwines
  the action `τ g` on the first factor with the action of `g` on
  `isotypicObj τ A`, because `φ` is an intertwining map.
- `isotypicEvaluation_galois τ Γ X γ`: as linear maps,
  `isotypicEvaluation τ X.V` composed with
  `LinearMap.lTensor U (multiplicityRepresentation τ Γ X γ)` equals
  `isotypicGaloisRepresentation τ Γ X γ` composed with
  `isotypicEvaluation τ X.V`. It is checked on pure tensors with
  `TensorProduct.ext'`.

## Proof outline

The functors are built from the published isotypic subrepresentation and
smooth subrepresentations, and from Mathlib's `Functor.mapAction` and
`Rep.ActionToRep`. Functoriality, naturality and the description of the
actions hold by `rfl`. The remaining results use the published membership
lemmas for isotypic parts, the intertwining property of morphisms of smooth
representations, and evaluation on pure tensors.

## Provenance

This is an internal construction. It extends the published isotypic parts
of `Langlands.Cohomology.HyperextDegenerationIsotypic` to smooth
representations with a commuting group action. Harris (1999), printed
pp. 312-313, the definition of `H^{n-1}(S_K(N), W)[π]`, formulas
(5.2)-(5.5) and Theorem 5.7, is motivation only.
