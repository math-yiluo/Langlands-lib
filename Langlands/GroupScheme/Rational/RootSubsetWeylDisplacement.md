# Character displacements of a root-generated Weyl subgroup

This internal supporting result concerns the actual character action of the
relative Weyl quotient. It is derived from the published definitions
`rootSubsetWeylGroup`, `IsRootReflection`, and `relativeWeylCharacterAction` in
`ClosedRootSubsetStatements` and from rationalization in
`Langlands.LinearAlgebra.RationalSpan`. It is an algebraic input to the
root-subset intersection argument; it does not prove that group-scheme
intersection statement.

Work over any field `k : Type u`, with a commutative group scheme `T`, a group
scheme `G` over `Spec k`, and a morphism `i : T.toGrp ⟶ G` whose underlying
scheme morphism is monic. For any subset `J` of the character lattice and
`w ∈ rootSubsetWeylGroup i J`, every character displacement
`relativeWeylCharacterAction i w χ - χ` lies in `Submodule.span ℤ J`.
Rationalization sends it into `ratSpan J`.
`RootSubsetWeylDisplacementStatement i` packages this rational containment, and
`rootSubsetWeylDisplacement` proves it. The results require no root-system,
convexity, splitness, maximality, or reductivity assumptions.

The integral proof uses subgroup closure induction with the character variable
generalized. A generating reflection has displacement
`-(latticePairing T χ c • β)` for a generating root `β ∈ J`, so its displacement
lies in the integral span. The identity has zero displacement. For a product
`x * y`, the displacement is the sum of the displacement of `x` at `y χ` and
that of `y` at `χ`. For `x⁻¹`, it is the negative of the displacement of `x` at
`x⁻¹ χ`. These formulas prove closure under multiplication and inversion
without requiring that the generating subset be preserved by the action.

For the rational conclusion, the inverse image under the additive
rationalization map of `ratSpan J`, viewed as an integral submodule, contains
`J` by `toRat_mem_ratSpan`. It therefore contains `Submodule.span ℤ J`.
Finally,
`characterDisplacement_mem_inf_ratSpan_of_mem_rootSubsetWeylGroup` applies the
rational conclusion twice: membership of `w` in both the `S` and `X`
root-generated Weyl subgroups puts every rationalized displacement in
`ratSpan S ⊓ ratSpan X`. This asserts containment in the intersection of spans;
it makes no identification with the span of the intersection of root sets.
