# Supports under flat extension of scalars

This internal construction supplies the flat support comparison needed for the coaction support step of the Serre criterion. The rings and module have independent universes. No finite generation hypothesis is imposed.

For any algebra, the support of its scalar extension is contained in the inverse image of the original support. Pure tensors span the scalar extension. At a support point, one such generator has annihilator contained in the prime. If the contracted prime were outside the original support, some scalar outside that prime would kill its module factor. Its image would then kill this pure tensor, contradicting the annihilator containment.

For the reverse inclusion under flatness, a support point of the original module supplies an element whose cyclic annihilator lies in the contracted prime. The cyclic module is a quotient of the base ring and injects into the original module. Flat scalar extension preserves this injection. The extended cyclic module identifies with the quotient of the new ring by the extended ideal. That ideal lies in the given prime, so the point belongs to the support of the quotient, and hence to the support of the extended module.

The construction `baseChangeSupportHomeomorph` packages the resulting equality as the identity homeomorphism between the two subspaces of the new prime spectrum. It is a derived result from the pinned Mathlib support, cyclic quotient, tensor quotient and flat injection APIs, implemented by Worker 101. It claims no coaction transport or invariant support result by itself.
