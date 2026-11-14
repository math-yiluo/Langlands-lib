# Vector-quotient series over an arbitrary affine base

This is an internal, derived interface for the affine cocycle argument in the proof of
Zariski-local conjugacy of split Borel subgroups. It introduces no assertion that any
particular reductive or unipotent group has such a series.

`HasAffineVectorSeries n H` means that `H` has a finite series of length `n` with
represented fppf vector-group quotients over `Spec R`. At length zero, the all-test
image of the identity of `H` is the trivial subgroup functor. At a successor, an
actual closed subgroup `j : K → H` and homomorphism `q : H → V` are supplied;
`RelativeRoot.IsFppfQuotient` says that `q` is flat, surjective, and locally of finite
presentation and that its actual kernel has the same all-test image as `j`.
The quotient `V` has natural additive coordinates in a finite number of global
functions, and the kernel has a shorter series. Kernel equality entails normality.
No smoothness or connectedness of the total spaces is imposed. In particular the
base ring may be disconnected or zero.

The vector-group cocycle lemma generalizes the published one-dimensional proof in
`SplitUnipotentTorsor.VectorCocycle`: for each coordinate, additive faithfully flat
descent on an affine cover gives a coboundary; these coboundaries are assembled using
the natural point-coordinate equivalence. This works also in dimension zero.

`HasAffineVectorSeries.cocyclesVanish` proves
`SplitUnipotentAffineTorsor.CocyclesVanish H` when `H` is affine and has the specified
series. The induction uses the published kernel and quotient argument in
`SplitUnipotentAffineTorsorProof`. Affineness passes to the closed kernel, the vector
quotient is affine, and the shorter series first gives a scheme section of `q`.
Twisting a cocycle by a lift of its trivialized quotient cocycle puts it in the
kernel, where the induction hypothesis applies.

`of_hasSplitSeries` forgets the extra smoothness, total-space connectedness and
normality conditions of the existing `RelativeRoot.HasSplitSeries`, and allows its
one-dimensional quotients as finite-dimensional vector quotients. This direction
of implication does not assert that every group with the new series satisfies
those extra conditions.

Shared declarations `Cocycle.isTrivial_of_isVectorGroupOfDimension` are imported from `Langlands.GroupScheme.SplitUnipotentTorsor.VectorRetract`; their mathematical hypotheses, conclusions and data are unchanged.
