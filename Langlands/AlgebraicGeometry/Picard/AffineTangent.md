# Affine tangent vectors and augmented dual-number maps

This internal adapter connects the project's actual scheme-valued tangent predicate
with Mathlib's affine spectrum equivalence. Let `K` be a field, `A` a commutative
`K`-algebra in the same arbitrary universe, and `r : A →ₐ[K] K` an augmentation.
The structure morphism is `Spec.algebraMap K A` and the rational point is `Spec(r)`.

For an algebra map `f : A →ₐ[K] DualNumber K`,
`isTangentVectorAt_spec_map_iff` identifies the tangent condition on `Spec(f)`
with `fstHom.comp f = r`. The condition of being over `K` follows from algebra
linearity; the base-point condition is the spectrum of the augmentation equation.
Faithfulness of `Spec` gives the converse.

`affineTangentEquiv` is an equivalence between the subtype of algebra maps with
this augmentation and the subtype of actual `Picard.IsTangentVectorAt` morphisms.
Its forward map is `Spec`; its inverse and inverse identities use the existing
Mathlib `Spec.homEquivAlgHom`, restricted by the augmentation condition.

`spec_map_eq_constant_tangent_iff` identifies the constant scheme tangent
`dualNumberProjection K ≫ Spec(r)` with the algebra map obtained by composing
`r` with the constant inclusion into the dual numbers. This follows from
contravariant composition and faithfulness of `Spec`.

The constructions are derived directly from the imported definitions and Mathlib's
fully faithful spectrum functor; no external theorem is transcribed. They impose
no algebraic-closure, finite-type, reducedness, or smoothness hypotheses. They
supply an affine interface and do not assert a closed-immersion criterion.
