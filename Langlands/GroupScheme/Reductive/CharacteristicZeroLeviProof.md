# Proof of characteristic-zero Levi decomposition

`Langlands.GroupScheme.characteristicZeroLeviDecomposition` proves the
unchanged Library proposition
`Langlands.GroupScheme.CharacteristicZeroLeviDecompositionStatement.{u}`
for every universe `u`. For every characteristic-zero field `F : Type u`
and group scheme `G` over `Spec F` with `IsAffine G.X.left` and
`LocallyOfFiniteType G.X.hom`, smoothness and connectedness give a group
scheme `L` over the same field and homomorphisms `p : G ⟶ L` and
`j : L ⟶ G` with `j ≫ p = 𝟙 L`. The group `L` is connected reductive.
The actual scheme-theoretic kernel `GroupScheme.kernel p` is smooth,
connected and unipotent.

The implemented proof applies
`characteristicZeroLeviDecomposition_of_reductiveVectorExtensions` from
`CharacteristicZeroLeviAssembly` to the published theorem
`characteristicZeroReductiveVectorExtension` from
`CharacteristicZeroVectorExtensionProof`. This discharges the assembly's
sole remaining premise and preserves the exact target and its universes.

The imported assembly uses the following algebraic inputs:

1. `ReductiveUnipotentQuotient.ofPerfectField` constructs the reductive
   quotient of `G` over `F`, using characteristic-zero perfectness,
   ground-field unipotent-radical existence, its represented fppf quotient,
   and the perfect-field pseudo-reductivity theorem. Its kernel comparison
   identifies the full scheme-theoretic kernel with the represented
   radical on every scheme test, transferring smoothness, connectedness
   and unipotence.
2. `CharacteristicZeroUnipotentExtension.exists_section` constructs a
   homomorphic section of that quotient by induction on the smooth
   relative dimension of its kernel. The published theorem
   `RelativeRoot.splitUnipotentStableVectorSubgroup` supplies a central
   vector subgroup stable under the extension group. Quotienting by it
   reduces the dimension. Pulling the smaller extension's section back
   leaves a vector-kernel extension of the reductive quotient.
3. `characteristicZeroReductiveVectorExtension` splits this vector-kernel
   extension over the original field. Its published proof obtains a
   normalized invariant integral from characteristic-zero complete
   reducibility, with dual fixed vectors descended from the algebraic
   closure, and averages the regular defect of a scheme section to obtain
   a group-scheme section.

The quotient and the section are the required `L`, `p` and `j`; the three
kernel properties come from the quotient construction. Every algebraic
input above is supplied by an imported theorem, so the final proof has
no additional hypothesis. Its provenance is internal composition of
published Library results; their companions record the algebraic
constructions and source provenance. The conclusion is exactly the
split-quotient formulation in `CharacteristicZeroLeviStatement`; it
asserts no uniqueness or conjugacy of sections.
