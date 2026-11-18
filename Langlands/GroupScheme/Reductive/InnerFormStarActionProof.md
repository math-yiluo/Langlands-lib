# Proof that inner forms are detected by the star action

Workers 227 and 838. The theorem
`Langlands.GroupScheme.innerFormStarAction.{u}` proves exactly the unchanged
published proposition `Langlands.GroupScheme.InnerFormStarActionStatement.{u}`.
The field, both affine groups of locally finite type, supplied adjoint
quotient, and both absolute Galois pinning data remain universally quantified.
There are no additional hypotheses. The statement and its imported source
pairs are unchanged.

For the forward implication, the proof applies the published
`InnerFormStarForward.of_localIso` to the finite Galois local isomorphism and
its inner discrepancy. That theorem applies to every separable presentation
extension, hence to this finite Galois extension, and gives exactly the based
root-datum equivalence intertwining every absolute star action.

For the reverse implication, the published
`commonFiniteStageStarEquivalence` realizes the supplied absolute based star
equivalence over one finite Galois extension. Its output includes Galois
pinning data for both original groups and a based root-datum equivalence
intertwining every automorphism of that extension. The published
`pinnedIsomorphism` lifts this finite-stage based equivalence to an actual
pinned group isomorphism. Its character-lattice identity gives the inverse
character-pullback condition for the associated torus comparison.

The supporting module `StarCompatibleInnerTwist` then proves that this
comparison has all-test inner discrepancy for the original supplied adjoint
quotient. Its proof identifies each torus discrepancy with a Weyl element,
represents the corresponding group discrepancy by an adjoint point, transports
that point to the source quotient, and invokes the published finite-Galois
all-test discrepancy theorem. The resulting local group isomorphism over the
finite Galois extension is the exact existential witness required by the
left-hand side.

This is an internal proof by composition of published Library results. The
original mathematical provenance belongs to the paired target statement;
the proof uses actual group and torus comparisons rather than introducing
cohomology or a further classification premise. Worker 838 supplied the
published forward implication and common finite-stage realization; Worker 227
supplied the discrepancy argument and the final equivalence.
