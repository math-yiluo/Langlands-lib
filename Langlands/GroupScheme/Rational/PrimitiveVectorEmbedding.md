# Closed vector embeddings from primitive algebra generators

Author: Worker 1552, task `f02d1dea-6430-41df-bf80-bd95f132e32f`.

This internal construction supplies the geometric assembly step for the embedding
clause of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Lemma B.1.10, printed pp.565–566 / PDF pp.591–592. The registered original is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The primitive-coordinate route is derived implementation material. It does not
assert that the structural hypotheses of B.1.10 already supply primitive algebra
generators.

The module reuses `HopfPrimitive.familyHom` from
`CommutativePTorsionVectorProof`: a finite family `y` of primitive elements of a
commutative Hopf algebra `A` over a commutative ring `R` gives an actual
group-scheme homomorphism `Spec A → VectorGroup.groupScheme R n`.

`isClosedSubgroup_familyHom` proves that this homomorphism is a closed immersion
when `Algebra.adjoin R (Set.range y) = ⊤`. The range of polynomial evaluation is
the generated subalgebra, so evaluation is surjective. Its spectrum map is
therefore a closed immersion.

`coordinates_familyHom` identifies the image on every relative scheme test,
including nonreduced tests: its coordinate at `i` is the pullback of the global
function corresponding to `y i`. The target's standard vector coordinates are
natural under arbitrary test-scheme maps by `VectorGroup.coordinates_comp`.

Over a field, `exists_closed_vectorEmbedding_of_primitive_generation` uses
`PTorsionHopf.exists_isPrimitiveGenerating` to extract finitely many primitive
generators from finite type and generation by all primitive elements, and then
applies the preceding construction. There is no smoothness, connectedness,
perfectness or characteristic assumption in this conditional assembly lemma.
Proving primitive generation from the exact B.1.10 hypotheses remains a separate
obligation of the task.

`closedVectorEmbeddingOfPrimitiveGeneration` packages this existence result as
data: it returns a natural number, a homomorphism to the standard vector group
of that dimension, and a proof that the homomorphism is a closed immersion.
The definition uses classical choice; the chosen embedding has the same
primitive-generation input as the existence theorem.
