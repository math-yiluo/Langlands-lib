# Geometrically integral fibres in algebraic terms

This module translates the hypothesis of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT)
from schemes to rings. The statement assumes that `Spec S → Spec R` is geometrically integral,
and the algebraic part of the proof uses that `K ⊗[R] S` is a domain for every field `K` over
`R`.

## Statement

`Langlands.CommutativeAlgebra.isDomain_tensor_of_geometricallyIntegral`: let `R` and `S` be
commutative rings in the same universe `u`, `S` an `R`-algebra, and assume
`AlgebraicGeometry.GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))`.
Then for every field `K : Type u` with an `R`-algebra structure, `K ⊗[R] S` is a domain.

The field `K` is in the universe `u` because Mathlib's `AlgebraicGeometry.geometrically`
quantifies only over fields in the universe of the schemes.

## Proof

Mathlib's `GeometricallyIntegral f` means `geometrically IsIntegral f`: every base change of `f`
along `Spec K → Spec R`, `K` a field, is an integral scheme. By
`AlgebraicGeometry.pullback_of_geometrically`, the pullback of `Spec S → Spec R` along
`Spec K → Spec R` is integral. `AlgebraicGeometry.pullbackSpecIso R S K` identifies this
pullback with `Spec (S ⊗[R] K)`, so that scheme is integral too (`IsIntegral.of_isIso`), and
`AlgebraicGeometry.affine_isIntegral_iff` gives that `S ⊗[R] K` is a domain. Finally
`Algebra.TensorProduct.comm R K S : K ⊗[R] S ≃ₐ[R] S ⊗[R] K` transfers the domain property to
`K ⊗[R] S`.

## Provenance

The lemma unfolds the definition of geometric integrality: for a scheme over a field this is
Stacks Project, Definition 33.9.1 (Tag 020H), and Mathlib's `GeometricallyIntegral` applies it to
all fibres of a morphism after any field extension. It is internal to the project; Worker 281
proposed the statement and Worker 928 proved it.
