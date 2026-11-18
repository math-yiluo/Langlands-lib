# Corestriction as a homomorphism of Brauer groups

Task 7532 (`Langlands.Algebra.BrauerGroup`) puts an additive abelian group law on Mathlib's actual matrix-stable Brauer quotient: the neutral class is the ground field, the sum is represented by the tensor product, and the negative by the opposite algebra. This module shows that the corestriction map `cor K L` of `BrauerClass` is an additive group homomorphism for this law. It is represented on actual central simple algebras by the tensor descent, and it is the identity for the identity extension. Here `L/K` is finite separable and `K`, `L` lie in one universe. There is no restriction on the characteristic.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

- `cor_classOf` computes `cor K L (classOf A) = classOf (corCSA K L A)`, for Task 7532's `classOf`. It holds by definition.
- `corCSATensorEquiv K L A B` is an actual `K`-algebra isomorphism `corCSA K L (tensor A B) ≃ₐ[K] tensor (corCSA K L A) (corCSA K L B)`, where `tensor` is Task 7532's tensor product of actual central simple algebras.
- `corHom K L : BrauerGroup L →+ BrauerGroup K` is corestriction as an additive group homomorphism, with underlying map `cor K L` (`corHom_apply`).
- `corHom_classOf` computes `corHom K L (classOf A) = classOf (corCSA K L A)`. The homomorphism is represented on actual central simple algebras by the tensor descent over the canonical closure.
- `corHom_zero` says that split classes go to split classes: `corHom K L 0 = 0`.
- `corHom_self F` says that corestriction along the identity extension `F/F` is the identity homomorphism.

## Implemented proof

**The zero class.** `map_zero` is `cor_groundField` of `BrauerClass`. Task 7532's zero is by definition the class of `groundField`.

**Additivity.** Choose representatives of the two classes. Task 7532 defines the sum to be the class of the tensor product. So it suffices that `corCSA K L (tensor A B)` and `tensor (corCSA K L A) (corCSA K L B)` are isomorphic. `corCSATensorEquiv` composes the following steps.

- Identity isomorphisms identify the bundled carriers with the underlying algebras.
- `corEquiv` from `Functoriality` transports between the two descents of `A ⊗[L] B`, built with the bundled and with the underlying instances.
- The inverse of `corMulEquiv` from `BrauerClass` maps the descent of `A ⊗[L] B` to the tensor product of the descents.

Mathlib's `Algebra.TensorProduct.congr` assembles these. Routing through `corEquiv` avoids a costly comparison of the two instance structures inside the tensor product of conjugates. Task 7532's `classOf_eq_of_algEquiv` concludes.

**The identity extension.** `corHom_self` is extensionality applied to `cor_self` of `Identity`.

## Sources and scope

J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13, identifies the class of the fixed algebra with the cohomological corestriction (formula (1)). The Remarque on printed p. 209 / PDF p. 14 allows that formula to be taken as the definition. With this definition, the homomorphism property is a consequence of multiplicativity of the tensor descent. That multiplicativity is proved here directly on actual algebras (`corMulEquiv`). The group law itself is Task 7532's and is not rebuilt here.
