# Inverse-character correction of all local pinning tests

`AffinePinningCorrectionCriterion` states a sufficient condition for correcting
an actual comparison between supplied pinned models over a common arbitrary
commutative coefficient ring `A`. The differential of the comparison carries
each chosen scalar-extended simple vector to a specified unit multiple of its
relabeled target vector. A supplied target coordinate-torus section over an
arbitrary scheme `W → Spec A` has the inverse simple-root values on every
compatible affine test. Composing the normalized pulled comparison with the
inner automorphism of that section then satisfies `PreservesLocalPinning`.
`affinePinningCorrectionCriterion` proves this proposition in every universe.

The construction uses `normalizedBasePointsEquiv` to express the target torus
section as a section of the actual direct pullback group. `affineSectionPoint`
evaluates a section on a compatible coefficient test; evaluation commutes with
the dual-number constant map. `preservesLocalPinning_corrected` derives each
local-test algebra structure and both original scalar towers from the actual
scheme base-map equations. Differential naturality extends the given unit
multiples to that test. The actual target weight-space equation and inverse
character value cancel these units. The normalized point equivalences identify
this differential calculation with conjugation on the original root-vector
points, giving the required equality on the direct pullbacks.

No affineness, connectedness or nonemptiness is assumed for `W`, and `A` need
not be local or nonzero. The sufficient condition explicitly requires the
torus section and its inverse character values; this unit does not construct
them or assert comparison existence. The content is internal coefficient and
pullback coherence, derived from the supplied pinning vectors, Lie-kernel
naturality, weight-space equations and actual inner-automorphism formulas.
It makes no new original-literature assertion.
