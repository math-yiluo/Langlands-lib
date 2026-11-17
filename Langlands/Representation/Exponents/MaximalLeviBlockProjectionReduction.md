# A conditional reduction for the maximal Levi block projection

This internal proof helper for Task 6621 retains
`RationalCuspidalInertiaDecompositionStatement.{u, max u v}` and
`MaximalLeviBlockStatements.{u, v}` as explicit hypotheses. It does not prove
either statement and does not discharge the requested unconditional target.
The target and every imported published module are unchanged.

`Langlands.Aubert.General.RepresentedParabolic.maximalLeviBlockProjectionEquivalenceOfDecompositionOfBlocks`
is a defined proof term for the full conditional reduction. It retains the
decomposition and block-statement hypotheses in that order and uses the
theorem described below.

`Langlands.CuspidalSupport.isRationalInertiaRelated_iff_linearEquiv` compares
the actual categorical unramified-twist relation with the linear-equivalence
formula used by `MaximalLeviBlockStatements`. A categorical isomorphism is
inverted to give an equivariant equivalence from the twist of the base
representation to the second representation. Twisting keeps the carrier,
so linearity gives precisely the displayed scalar identity. The reverse
construction packages that scalar identity as an equivariant equivalence
and then inverts the resulting smooth isomorphism.

`Langlands.CuspidalSupport.rationalInertiaBlock_isRightAdjoint_of_representedCuspidal`
applies the decomposition hypothesis to an arbitrary connected reductive
group with an irreducible representation whose normalized Jacquet modules
vanish along all proper represented parabolics. It chooses a maximal split
torus extending the trivial torus and a generic cocharacter. The published
`standardCocharacter`, `relativeRootSystem`, closedness of standard
unipotent point subgroups, and `rationalPoint_t2Space` discharge the
structural inputs. The published represented-to-standard cuspidality theorem
discharges the cuspidality input. The internal categorical decomposition
helper then gives a left adjoint to the block inclusion.

`Langlands.Aubert.General.RepresentedParabolic.maximalLeviBlockProjectionEquivalence_of_decomposition_of_blocks`
proves the exact target under the two stated hypotheses, at its original
universes. For clause (a), the linear-equivalence comparison identifies the
target's Levi block with the actual rational inertia block. The preceding
conditional helper applies on the rational Levi with its canonical topology
and the published Levi local compactness and nonarchimedean instances.

For clause (b), the third part of the block-statement hypothesis supplies
full faithfulness of induction on the Levi block, its image in the group
block, and essential surjectivity onto that block. The internal
`fullSubcategory_adjunction_equivalence` helper applies to the composite
of the published first adjunction with any supplied block projection
adjunction. It provides faithfulness of the exact functor `rD`, invertibility
of the exact ambient adjunction unit, and the required equivalence and
natural isomorphism for its inverse.

All three lemmas are internal interface and categorical deductions from
published definitions and explicitly retained hypotheses. The file makes no
new assertion about the source beyond those definitions. Publication of
unconditional proofs of both prerequisite statements is still required
before this reduction can yield the task's final proof.
