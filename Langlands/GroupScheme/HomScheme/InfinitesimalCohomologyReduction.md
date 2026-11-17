# Conditional assembly of infinitesimal lifting from cohomology

`multiplicativeTypeInfinitesimalLift_of_cohomology` concludes exactly the unchanged Library proposition `Langlands.GroupScheme.MultiplicativeTypeInfinitesimalLiftStatement.{u}` from four explicit inputs:

- `MultiplicativeTypeLowDegreeVanishingStatement` for all commutative rings and multiplicative-type groups in the fixed universe.
- `SquareZeroHomomorphismCohomologyStatement`, the geometric deformation bridge for flat affine sources and smooth targets.
- Flatness of the structure morphism of every multiplicative-type group scheme over every base in that universe.
- Affineness of the structure morphism of every such multiplicative-type group scheme.

For each affine square-zero test, the proof applies base-change stability of the multiplicative-type predicate. The geometry inputs give a flat affine source on the unreduced affine test. The cohomology input gives vanishing for the reduced source. The geometric bridge then yields the specified-conjugator property. The existing `multiplicativeTypeInfinitesimalLift_of_squareZero` theorem completes nilpotent induction and extracts actual homomorphism lifts and kernel conjugacy.

This is an internal formal assembly from the named inputs and the published base-change stability of multiplicative type. It introduces no source assertion. All four prerequisites are hypotheses, so the theorem is a conditional reduction and supplies no unconditional proof of the task target.
