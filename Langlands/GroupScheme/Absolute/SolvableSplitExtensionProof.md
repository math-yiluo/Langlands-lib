# Homomorphic splitting of the torus quotient of a solvable group

Worker 1435.

`Langlands.GroupScheme.solvableSplitExtension` proves the published proposition
`Langlands.GroupScheme.SolvableSplitExtensionStatement.{u}` for an arbitrary
universe `u`, with no additional premise.

Let `k : Type u` be an algebraically closed field of any characteristic, and
let `H` be a smooth connected solvable affine group scheme over `Spec k`.
Suppose `i : U ⟶ H` is a closed subgroup with `U` smooth, connected and
unipotent, its range is normal, and `q : H ⟶ D` is a represented fppf quotient
by that range onto a split torus. The conclusion is
`∃ σ : D ⟶ H, σ ≫ q = 𝟙 D`. Here `σ` is a morphism in the category of group
schemes, so it preserves the group operations.

## Implemented proof

The proof applies the existing Library theorem
`solvableSplitExtension_of_oneDimensional` to the proved classification
`perfectFieldOneDimensionalUnipotent`. The former has type
`PerfectFieldOneDimensionalUnipotentStatement.{u} →
SolvableSplitExtensionStatement.{u}`; the latter proves its premise at the
same universe. Thus the resulting theorem has exactly the target type.

The [splitting reduction](SolvableSplitExtensionOneDimensional.md) first uses
Lie–Kolchin to embed `H` as a closed subgroup of an upper triangular group.
The classification, together with the existing closed-subgroup theorem and
the algebraically closed splitness reduction, shows that `U` is split
unipotent. Triviality of split-unipotent torsors over affine schemes gives a
scheme section of `q`. The kernel clause of `IsFppfQuotient` identifies its
kernel with the range of `i` on every test scheme.
`IsSplitTorus.exists_section_of_triangular` then corrects the scheme section
to a group-scheme homomorphism with the required section equation.

The [one-dimensional classification proof](../Unipotent/OneDimensional/Proof.md)
constructs a primitive polynomial coordinate and the corresponding
isomorphism to the one-dimensional vector group over a perfect field.
Algebraically closed fields satisfy the perfect-field hypothesis needed in
the reduction.

## Provenance and scope

This module packages those published Library results into the exact
proposition documented in
[the target statement](SolvableSplitExtensionStatement.md). Its source is
J. S. Milne, *Algebraic Groups* (2017), Theorem 16.26(a), printed
pp.332–333, and Summary 16.29(b), printed p.334; registered source
`milne-2017-algebraic-groups`. The implemented proof uses the Library's
triangular section correction described above.

The target pair and all of its imported pairs are unchanged. The proof does
not use `SolvableMaximalTorusSemidirectStatement`,
`MaximalTorusConjugacyStatement`, `SolvableMaximalTorusConjugacyStatement`,
or their proof families.
