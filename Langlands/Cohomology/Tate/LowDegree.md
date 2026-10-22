# Actual Tate degree minus two and abelianization

Author: Worker 45.

Let `G` be a finite group and `A` a representation of `G` over a commutative
ring `R` on which `G` acts trivially. `minusTwoTensorEquiv A` is Mathlib's
comparison `TateCohomology.isoGroupHomology (-2) 1` from Tate degree minus
two to ordinary first group homology, composed with Mathlib's proved
`groupHomology.H1AddEquivOfIsTrivial`. Its target is the tensor product over
the integers of the additive group underlying the actual group
abelianization and the coefficient group.

`minusTwoClass A g a` is the Tate class in degree minus two corresponding,
under Mathlib's inverse comparison, to the first-homology class of the
single chain at `g` with coefficient `a`. The lemma
`minusTwoTensorEquiv_class` says that `minusTwoTensorEquiv A` sends it to
`Additive.ofMul (Abelianization.of g) ⊗ₜ a`. This representative formula
follows from Mathlib's corresponding first-homology formula and the inverse
laws of its Tate comparison.

For the actual trivial representation `integralTrivial G` over
`ULift.{u} ℤ`, `integralTensorEquiv G` removes the tensor factor using the
explicit ring equivalence of the lifted integers with the integers.
The resulting additive equivalence `integralMinusTwoEquiv G` identifies
actual Tate degree minus two with `Additive (Abelianization G)`. By
`integralMinusTwoEquiv_class`, the class `minusTwoClass` at a group element
with coefficient one maps to that element's abelianization class.

For a subgroup `H`, the file also names the two group-theoretic maps
on abelianizations: `abelianizationInclusion H`, which is
`Abelianization.map` applied to the subgroup inclusion, and
`abelianizationTransfer H`, which is Mathlib's `MonoidHom.transfer`
to the abelianization of `H`, descended through the universal property
of the abelianization of `G`. This file does not relate them to Tate
corestriction or restriction; those comparisons are separate theorems.

The coefficient carriers and group remain in arbitrary universe `u`.
The tensor equivalence uses the supplied equivalence of lifted integers
with integers; it does not replace the scalar ring by a Type-0-only
interface.

Source: Serre, *Local Fields* (1979), Chapter VIII, section 1,
printed pp. 127–129 (PDF pp. 133–135), for the comparison with shifted
homology (in particular `Ĥ^{-2}(G, ℤ) = H_1(G, ℤ) = G^{ab}`), and
Chapter VII, section 8, Proposition 7, printed pp. 120–121
(PDF pp. 126–127), for the group-theoretic transfer `Ver : G/G' → H/H'`;
Chapter VII, section 7, printed pp. 118–119 (PDF pp. 124–125), gives the
subgroup map conventions. The implementation
reuses the actual pinned Mathlib low-degree homology equivalence and
group-theoretic transfer. Source ID `serre-1979-local-fields`,
retained PDF SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
