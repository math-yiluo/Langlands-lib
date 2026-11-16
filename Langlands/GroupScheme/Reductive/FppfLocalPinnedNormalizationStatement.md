# Statement: geometric fppf-local normalization of actual comparisons

`FppfLocalPinnedNormalizationExistenceStatement` isolates a geometric
prerequisite for the relative pinned comparison theorem. Given supplied affine
pinned split reductive models, maps from an arbitrary common scheme to their
original bases, and an actual comparison of their pullbacks, there should be
one flat surjective cover locally of finite presentation with the following
data: an actual comparison `d` satisfying `IsLocallyPinned`, and an actual
point `c` of the source pulled-back group whose inner automorphism equals the
discrepancy `pullComparison e q ≪≫ d.symm`.

The predicate retains the exact torus and positive-coroot cocharacter equations
and the actual dual-number simple pinning points on every local affine test.
Root relabellings may vary with these tests. The statement selects no global
constant root-datum equivalence. The original affine model bases may differ;
the common scheme and covering scheme have no connectedness, nonemptiness,
affineness or quasi-compactness hypotheses. The pullback is the actual
normalized `pullComparison`.

This is an internal local consequence of Conrad, *Reductive group schemes*
(2014), Theorem 6.1.17, p.197, and Theorem 7.1.9(3) and its proof, pp.245–246,
rather than a literal restatement of either theorem. Locally identifying the
two pinned models reduces the comparison to the pinned automorphism
decomposition. An adjoint correction point lifts to the original group after
a further fppf cover. The source discusses nonempty bases; a proof of the
present statement must also handle the empty case directly.

Only local existence is requested. There is no uniqueness, independence,
composition, pullback law or global full-centre quotient section in this
statement. Those are separate steps in the parent construction. This module
states the prerequisite as a proposition; it does not prove it.
