# One polar compact subgroup for all actual dynamic parabolics

Authors: Worker 1359 and Worker 1571.

This internal derived construction combines `AffinePolarCompact` with
`Dynamic.ConjugatedParabolicPolarCover`. Let `k : Type u` be a field,
`S : Type u` an `RCLike` field with a `k`-algebra structure, and `G` an affine
group scheme over `Spec k`. A supplied representation
`ρ : MatrixRepresentation G (Fin d)` is a scheme-theoretic closed immersion,
and its image on actual `S`-valued affine points is stable under conjugate
transpose. The integer `d` may be zero. The point carrier and topology are
literally `G.affinePoints (CommAlgCat.of k S)` and its existing topology induced
by evaluation of all regular functions.

The compact subgroup is constructed from these data: it is the inverse image
under `ρ.affineMatrix` of the unitary matrix group.
`parabolic_mul_affineMaximalCompact_eq_univ` proves that every actual
cocharacter's dynamic parabolic, followed by this subgroup, covers the point
group. The compactness input comes from the constructed `affineMaximalCompact`.
For each actual point, `exists_affineUnitary_right_quotient_posDef` gives a right
quotient by an element of the same subgroup with positive definite matrix.
Positive definiteness implies the Hermitian condition required by the arbitrary
cocharacter covering theorem. This is the entire new proof step; arbitrary
algebraic diagonalization and its two-limit cancellation are supplied by that
imported theorem.

`range_mul_affineMaximalCompact_eq_univ` substitutes the defining range equality
of any actual group-scheme morphism representing the dynamic parabolic.
Consequently the left factor is the literal range of `P.affinePointsTarget p`,
and the right factor remains the same constructed compact subgroup.

`affineDynamicIwasawa` bundles compactness, maximality against every compact
overgroup, and this range covering for every cocharacter and every actual
representative. One subgroup works for all those choices. The value lemma is
definitional: the constructed subgroup is exactly `affineUnitarySubgroup`.
No parabolic is required to be proper or split, and no cocharacter is required
to be nontrivial.

This pair makes no new external literature assertion. It composes the actual
polar construction and the dynamic covering theorem; the companion descriptions
of those imported results explain their proofs. It remains an intermediate
conditional result. It does not prove that an arbitrary connected reductive
group has an adjoint-stable closed representation, or that every geometric
parabolic is represented by a dynamic parabolic. The full archimedean Iwasawa
proposition retains both existence and classification obligations and all its
original hypotheses.
