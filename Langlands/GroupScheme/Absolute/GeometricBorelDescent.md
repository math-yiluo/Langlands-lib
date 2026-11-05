# Descent of an actual geometric Borel subgroup

This supporting unit constructs an actual ground-field geometric Borel from
an algebraic-closure Borel whose subgroup functor agrees on the canonical
fpqc overlap. It works for every field `k : Type u` and every group scheme
`G` affine over `Spec k`. It assumes an actual inclusion
`i : H ⟶ G` after base change to `AlgebraicClosure k`, with
`IsBorelSubgroup i`, and equality of the two overlap ranges on **all test
schemes**. It does not replace this equality by invariance of rational points.

`GeometricBorelDescentData i` records the descended group, its inclusion in
`G`, affineness, `IsGeometricBorelSubgroup`, an actual isomorphism from its
algebraic-closure pullback to `H`, and the exact equation identifying the
base-changed inclusion with that isomorphism followed by `i`.
`IsBorelSubgroup.descentOfOverlap` selects such data from the given overlap
equality. No uniqueness or canonical choice is asserted.

The proof first establishes
`IsBorelSubgroup.of_baseChange_toAlgebraicClosure`. A closed inclusion whose
algebraic-closure pullback is Borel is Borel over the original field.
Smoothness and connectedness reflect by the published fpqc reflection
lemmas. Geometric solvability follows from
`isSolvableGroupScheme_iff_rationalPoints` over the algebraically closed
field. To check maximality, base change any ground-field smooth connected
solvable closed overgroup. It is affine because it is closed in the affine
ambient group. Its pullback remains connected by the smooth affine
connectedness theorem, and remains solvable by
`solvableFieldExtensionStatement`. Geometric maximality makes the
base-changed factor map an isomorphism; `isIso_of_baseChange` reflects this.
The companion lemma then gives both parts of the Library predicate
`IsGeometricBorelSubgroup`.

For the construction, the published
`IsClosedSubgroup.exists_descent_of_overlap_range_eq` supplies the actual
affine ground-field subgroup, closed inclusion, recovery isomorphism and
inclusion equation. `IsBorelSubgroup.iso_comp` transports the prescribed
Borel structure across the recovery isomorphism. The reflection lemma gives
the ground-field Borel structure, completing the data.
`isQuasiSplit_of_borel_overlap_range_eq` packages this construction for a
connected reductive ambient group.

This is an internal derivation from the Library modules
`Descent.ClosedSubgroups`, `Reductive.QuasiSplit`,
`Rational.UnipotentRadicalProperties`,
`Absolute.ParabolicBorelFactorization`,
`Absolute.SolvableFieldExtensionProof`, and their imported transport and
base-change reflection results. It introduces no external structural
assertion. Producing an overlap-invariant Borel over a finite field,
including the conjugacy, Frobenius and finite-model steps, remains a
separate obligation. This unit proves neither `FiniteFieldQuasiSplitStatement`
nor the host `FiniteFieldCentralCocharacterSolvableStatement`.
