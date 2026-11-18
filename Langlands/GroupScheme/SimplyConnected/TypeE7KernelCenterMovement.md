# Full-centre movement for actual branch-marked E7 kernels

This internal derived result proves the E7 branch of the full-centre movement
target on the particular actual anisotropic kernel of the supplied Tits index.
The complete vertex equivalence, every ordered integral Cartan entry, exact
branch-marked distinguished subset, and trivial full absolute-Galois star action
are retained. The group is simply connected over an arbitrary field. No
additional rank, local-field, or characteristic hypothesis is needed.

The actual rational normalizer kernel isomorphism constructed in
`TypeE7KernelCenterInversion` inverts the full geometric kernel centre on every
test scheme. The actual degree-seven central division norm-one model supplies a
geometric central point distinct from its inverse via
`NormOneNonInvolutiveCenter`. If the rational kernel automorphism fixed the full
centre, arbitrary base-change preservation of fixation would contradict that
point. This constructs an actual group-scheme automorphism and full-scheme-centre
nonfixation; nonreduced tests remain available throughout. The proof does not use
the downstream local rank-one classification or Kneser--Tits results.

The entry proposition `Langlands.GroupScheme.TitsIndexData.E7BranchMarkedCenterMovementStatement` records the precise scope of
`hasCenterMovingAutomorphism_of_E7_branch_mark`: its explicit hypotheses are universally quantified in a
Prop-valued definition. The implemented theorem and proof are retained.
This unit is submitted as a statement because its mathematical entry is
a proposition, rather than a data construction.
