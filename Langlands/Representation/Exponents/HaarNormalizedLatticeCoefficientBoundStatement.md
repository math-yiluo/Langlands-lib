# Coefficient decay relative to actual inverse Haar modulus weights

Author: Worker 19. This is a derived internal statement for the general
rational strict Jacquet criterion.

`Langlands.HaarNormalizedLatticeCoefficientBoundStatement` concerns a smooth
admissible complex representation of a locally compact nonarchimedean group.
The group, representation and finite index universes are independent. The
index type may be empty. A compact open subgroup fixes the vector and dual
functional whose coefficient is estimated.

The lattice is an actual monoid homomorphism from the multiplicative version
of `I → ℕ` into the group. The displayed common lower-middle-upper
factorization and three conjugation inclusions ensure multiplicativity of
its actual compact compression. These geometric conditions are premises.
For each coordinate ray, separate closed unipotent, Levi and opposite
subgroups are supplied, together with an actual Iwahori contraction basis.
The ray generator is the image of a supplied full-center Levi element, and
the same compact open subgroup satisfies the displayed Iwahori contraction
condition for that element.

Every full-center exponent of the actual normalized Jacquet module must have
norm strictly below one at the supplied ray element. This uses the existing
uniform generalized-character predicate, including its open-kernel condition.
There is no global finite-length or irreducibility premise.

The conclusion supplies positive real numbers `a i` and a positive constant
`C` bounding every lattice coefficient by `C * ∏ i, a i ^ n i`. For each ray,
`a i ^ 2 * δ i ⁻¹ < 1`, where `δ i` is exactly the positive real value of
`HaarModulus.closedRestrictCharacter` on its actual closed subgroup at that
ray element. Thus the weight is the inverse actual Haar modulus, with its
orientation fixed by the existing Haar character construction.

The internal derivation first sends each compression eigenvalue to a
full-center exponent of the actual normalized Jacquet module. If `q i` is
the actual inverse-half-modulus value, the strict spectrum condition gives
`‖μ‖ < ‖q i‖⁻¹`. Finite-dimensional power estimates give intermediate positive
radii strictly below these thresholds and the product coefficient bound.
The identity `‖q i‖² = δ i ⁻¹` gives the displayed weight inequalities.

This statement supplies no reductive-group realization of the geometric
conditions, no double-coset volume comparison, and no square-integrability
conclusion. Those remain obligations when applying it to the unchanged
rational-point criterion. Its derivation uses no classification, geometric
lemma, adjointness, character independence or cuspidal support assertion.
