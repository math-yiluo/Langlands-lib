# Preservation of closed immersions by analytification

`monicPullbackLimitOfEtaleSourceCover` constructs the universal lift into
a proposed pullback with a monic projection. It assumes localized étale
pullbacks and the analytic Hom sheaf property. Pulling the source cover
back to a test cone gives an étale cover of the cone vertex, using
compatible point lifting for joint surjectivity. The supplied affine
or other local pullback squares lift each piece to the proposed
pullback. Monicity makes the local lifts agree on overlaps. Analytic Hom
descent produces the lift, and separatedness on the same cover verifies
its projection identities. Monicity gives uniqueness.

This construction is an internal consequence of the localized point
lifting and site interfaces, with the stated descent premises.

For a representable closed immersion, pulling back along an affine test
point gives the spectrum of a quotient of its test algebra. The affine
closed immersion criterion for schemes gives this quotient and its
isomorphism over the affine test.

To compare an affine represented pullback with the proposed analytic
pullback, take the affine étale cover of the source analytification.
Separatedness of the algebraic target gives the affine overlap of each
source test with the target test. The algebraic universal property
factors this overlap through the represented pullback. On analytifying,
the affine pullback axiom gives the needed local square and naturality
identifies the composed projections. The limiting cone construction
then gives the analytic pullback whenever its projection to the target
test is monic.

Assume analytification takes surjective affine algebra maps to analytic
closed immersions. The quotient maps then give closed immersions and
thus monic projections on the affine target tests. The maps of the
étale target tests are jointly surjective, so analytic étale target
descent for closed immersions gives the original analytic closed
immersion. This direction assumes localized étale pullbacks, analytic
Hom descent, affine closed immersion preservation, and analytic
closed immersion target descent.
