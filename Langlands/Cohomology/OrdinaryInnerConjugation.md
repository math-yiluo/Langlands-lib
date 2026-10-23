# Inner conjugation on ordinary degree-two cohomology

This module constructs the inner-conjugation map on Mathlib's actual ordinary group cohomology and proves that its degree-two component is the identity. The coefficient ring `k` is commutative, `G` is any group, both are in a common arbitrary universe, and `A : Rep k G` is an arbitrary representation. No finiteness, topology, trivial-action assumption, or normalization of cocycles is required.

For `a : G`, `innerConjugation a` is the group homomorphism `g ↦ a * g * a⁻¹`. The representation morphism `innerConjugationCoefficient A a : Rep.res (innerConjugation a) A ⟶ A` is the action of `a⁻¹`. Its equivariance follows by associating the group products. `innerConjugationMap A a n` applies Mathlib's `groupCohomology.map` to these two maps. In degree two it sends a cocycle `f` to

`(g,h) ↦ A.ρ a⁻¹ (f (a*g*a⁻¹, a*h*a⁻¹))`.

The auxiliary one-cochain `innerConjugationBoundary A a f` is

`g ↦ A.ρ a⁻¹ (f (a*g*a⁻¹,a) - f (a,g))`.

The theorem `innerConjugationBoundary_d` proves that its ordinary differential is the transformed cocycle minus the original cocycle. The implementation rewrites the action terms and applies the two-cocycle equation at the three triples `(a,g,h)`, `(a*g*a⁻¹,a,h)`, and `(a*g*a⁻¹,a*h*a⁻¹,a)`. Adding the third equation, subtracting the second, and adding the first produces precisely the required difference. All remaining rearrangements use the abelian-group laws.

The theorem `innerConjugationMap_two` identifies the actual morphism on `groupCohomology A 2` with its identity morphism. It cancels the epimorphism `H2π`, uses `H2π_comp_map` to reduce to cocycles, and uses `H2π_eq_iff` with the displayed boundary witness. `innerConjugationMap_two_apply` is its evaluation form.

This is an internal derivation from Mathlib's ordinary cohomology functoriality, cocycle differential, and quotient API. It introduces no literature-dependent assertion or new assumption. The boundary formula and proof are implemented directly with inhomogeneous cochains; the module does not import or identify continuous cohomology with ordinary cohomology. This supporting unit does not establish finite-place choice independence, any local invariant law, or `GlobalInvariantStatement`.
