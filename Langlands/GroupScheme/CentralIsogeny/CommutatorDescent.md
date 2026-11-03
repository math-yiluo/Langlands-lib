# Descent of commutators through a homomorphism with central kernel

This module constructs, for a homomorphism of group schemes `π : C ⟶ G` over a base
scheme `S` whose full scheme-theoretic kernel is central, the morphism of schemes over `S`

    CommutatorDescent.hom π hπ : G × G ⟶ C

sending a pair of points `(π x, π y)` of `G` to the commutator `x y x⁻¹ y⁻¹` in `C`. It is
the scheme-theoretic form of the elementary fact that a central extension has a
well-defined commutator pairing on its quotient. Nothing in this module depends on fields or
on smoothness: the base `S` is arbitrary.

## Group-theoretic lemma

`commutator_mul_central` is the identity

    (a z)(b w)(a z)⁻¹(b w)⁻¹ = a b a⁻¹ b⁻¹

in an arbitrary group, for `z` and `w` commuting with every element. It is proved by a
direct calculation with `group` and the two commutation relations.

## Compatibility with the homomorphism

`tensorHom_commutatorMap` states that `(π × π) ≫ comm_G = comm_C ≫ π`, where
`comm_G = commutatorMap (𝟙 G) (𝟙 G)` is the published commutator morphism
`G × G ⟶ G` of `GroupScheme/ImageGenerationCommutator`. Both sides are compared through
the published points formula `commutatorMap_points`; the rest is the fact that `π` preserves
multiplication and inversion of points.

## Invariance under central translation

Hypothesis `hπ : IsCentral (kernelι π)` says the actual kernel of `π` lies in the
all-test-scheme centre of `C`.

- `commutator_eq_of_quotient_eq`: if two `T`-points `x, y` of `C × C` have the same image
  under `π × π`, then `comm_C` agrees on them. Writing `x = (a, b)` and `y = (a', b')`, the
  points `a⁻¹ a'` and `b⁻¹ b'` are killed by `π`, hence central by
  `isCentral_kernelι_iff`, and the group lemma applies in the group of `T`-points.
- `scheme_commutator_eq_of_quotient_eq` is the same statement for arbitrary morphisms of
  schemes `Z ⟶ (C × C)`, obtained by regarding `Z` as an object over `S` through `x`.

## The descent

From here on `π` is quasi-compact, flat and surjective on underlying schemes (instance
arguments). Every central isogeny satisfies these.

- `effectiveEpi_tensorHom`: the underlying scheme morphism of `π × π` is quasi-compact,
  flat and surjective. These properties are stable under base change and composition,
  through Mathlib's `MorphismProperty.pullbackMap` for the fibre product over `S`. By
  Mathlib's fpqc descent (`Mathlib.AlgebraicGeometry.Sites.Fpqc`) it is therefore an
  effective epimorphism of schemes.
- `epi_tensorHom`: consequently `π × π` is an epimorphism over `S`.
- `schemeHom` is `EffectiveEpi.desc` applied to `comm_C`. The descent condition is
  `scheme_commutator_eq_of_quotient_eq`. `fac_schemeHom` is the factorization.
- `hom` upgrades `schemeHom` to a morphism over `S`. Compatibility with the structure maps
  follows by cancelling the epimorphism `π × π`.

## Exported properties

- `fac`: `(π × π) ≫ hom π hπ = comm_C`.
- `lift_hom`: for `T`-points `x, y` of `C`, `(π x, π y) ↦ x y x⁻¹ y⁻¹`.
- `hom_comp`: `hom π hπ ≫ π = comm_G`. Proved by cancelling the epimorphism `π × π`
  and using `tensorHom_commutatorMap`.
- `one_hom`: the identity pair goes to the identity. This is `lift_hom` at `x = y = 1`.

No result here is an original-literature theorem. The module is internal infrastructure for
the proof of `CentralIsogenyCommonSemisimpleRefinement`.
