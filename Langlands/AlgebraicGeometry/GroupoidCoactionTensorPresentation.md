# Tensor coordinates for a published groupoid coaction

This internal adapter uses the unchanged published `GroupoidCoaction`.
Let `A → B → C` be commutative algebras, let `t : B →+* C`, and let
`e : C ≃ₐ[B] B ⊗[A] B` send `t(b)` to `1 ⊗ b`.
For a `B`-module `M` with compatible `A`-action, the module coordinate
change sends `e⁻¹(b₁ ⊗ b₂) ⊗ m` to `b₂ ⊗ b₁m`.
It is the composite of tensor symmetry, tensoring the algebra
equivalence, cancellation of scalar extension, and tensor symmetry.

Tensor balancing shows that the source and target maps agree on `A`.
Consequently the published additive coaction is `A`-linear. Composing
it with the coordinate change gives `presentationCoaction`.
Its fixed elements are exactly the original invariant subgroup.
When `t` is a ring étale equivalence relation, its identity point and
the published counit show that the original coaction, and hence the
coaction in coordinates, is injective.

These are derived coordinate constructions. This module does not prove the iterated-tensor identity from the published
cocycle law. That identity remains a separate obligation before applying
the flat tensor zero-detection lemma.
