# Nonempty relative roots before quasi-split splitting

The internal helper
`Langlands.GroupScheme.IsQuasiSplit.relativeRoots_nonempty_of_isAbsolutelyAlmostSimple`
proves that every actual maximal split torus of a quasi-split absolutely
almost-simple group has a relative root. The field has arbitrary characteristic
and universe. The conclusion does not assume that the group is split, that the
supplied torus is an absolute maximal torus, or that its relative roots have
already been shown reduced or simply laced.

The accompanying noncomputable definition
`Langlands.GroupScheme.IsQuasiSplit.relativeRootOfIsAbsolutelyAlmostSimple`
chooses an element of this actual relative-root set using the proved
nonemptiness. It constructs a root under the same hypotheses and retains its
nonzero-weight membership certificate.

The proof extends the supplied closed split torus to an absolute maximal torus
using `exists_maximalTorus_extension_of_finiteType`. The theorem
`torusFiniteGaloisSplitting` supplies a finite Galois field over which that
containing torus splits. Absolute almost-simplicity persists under this algebraic
extension by `IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`, and
`maximalTorusBaseChange` preserves maximality of the containing torus.
`IsAlmostSimple.relativeRoots_nonempty_of_split_maximalTorus` then supplies an
actual root over the splitting field: empty roots would make the maximal torus
an isomorphism and contradict noncommutativity of the almost-simple group.

Finally `IsQuasiSplit.rootRestriction` sends that root to an actual relative root
of the originally supplied split torus over the original field. Its nonzero
restriction uses quasi-splitness and the full torus centralizer; no root is
silently discarded. This is an internal deduction from the imported results,
rather than a transcription of a new literature assertion.

This helper supplies the nonemptiness input for the irreducibility step in the
building part of Kaletha–Prasad Theorem 10.3.1, before the argument establishes
splitting. It proves neither the supporting ordinary derivative or stable
chamber statements nor the host affine-diagram target.
