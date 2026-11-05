# Local irreducibility from actual two-Jacquet and modulus inputs

This is a derived conditional assembly on the actual rational-point family.
It does not prove `RationalRankOneSelfAssociationStatement`. The independent
universes `u` and `v` are retained, with inducing carrier universe
`max (u + 1) v`. The ambient topology is the canonical `pointTopology`.

The maximal standard index, point-normalizer and point-centralizer comparisons,
actual Coxeter data, root-length and simple-reflection comparisons, actual
Levi–Weyl identification, minimality and association laws, relative roots,
standard Levi conjugation, specified longest lift and standard cocharacter
remain explicit. The inducing representation is admissible and irreducible.
The actual same-parabolic and associated Jacquet modules of its induction
are assumed irreducible, and the associated module is assumed admissible.
An irreducible-subquotient detector, Jacquet vanishing outside these two
indices and the full index, and a full unitary central character on the
whole induction also remain inputs.

The two full-center scalar characters are constructed by admissible Schur,
using `inductionTwoJacquetScalarCharactersOfSchur`. The input `hchars` says
that these particular constructed characters are related by the specified
longest-lift conjugation. This comparison is assumed: this file does not
construct the associated geometric Jacquet isomorphism.

The retained global inputs are the exact propositions
`RationalStrictJacquetSquareIntegrabilityStatement`,
`RationalOppositeHaarReciprocityStatement`,
`DynamicParabolicQuotientCompactStatement`,
`RationalParabolicModulusStatement`,
`StandardCocharacterStatement`, `StandardLeviSplitComponentStatement`
and `CenterSplitComponentCompactnessStatement`. Literal Levi and parabolic
closedness, continuous parabolic projection, and the stated ambient local
compactness, Hausdorffness and nonarchimedean structure remain explicit.
For the unit-modulus case, the inputs also specify a central scheme
homomorphism into the actual Levi scheme with finite-index split valuation
image, and compact smooth-dual coefficients of the inducing object
restricted to that Levi's canonical common norm kernel.

`isIrreducible_standardInduction_of_twoJacquet_modulus_inputs` proves actual
normalized induction irreducible by contradiction. Compactness of the
parabolic quotient gives whole-induction admissibility. The full parabolic
modulus proposition gives ambient unimodularity. No extra premise supplies
either fact. Splitness of the maximal torus supplies its affineness.

Assuming induction reducible, `inductionTwoJacquetFactors` constructs its
actual proper nonzero invariant subspace and quotient, with the asymmetric
two-Jacquet support pattern. Compact-limit properties of the radicals
follow from the standard-cocharacter proposition. The constructed Schur
characters have open kernels, and their ambient-center moduli are one by
inheritance from the whole induction. The actual associated-character
modulus theorem then gives three cases. A strict first or second character
contradicts the respective obstruction in `RationalStrictFactorUnitarity`.
In the remaining case the first character has modulus one on the literal
central torus. `leviNormKernelPositiveForm_of_centralTorus` extends this to
the full center and constructs a positive form on the original inducing
carrier from its compact norm-kernel coefficients. Unitary induction with
a simple same-parabolic Jacquet module is irreducible, the final contradiction.

`twoJacquetStandardInductionSubrepresentationEquiv` turns the resulting
irreducibility into the actual inclusion equivalence from any nonzero
invariant subspace to the whole induction.

No self-normalization or self-association premise is introduced. The
filtration, simple-Jacquet, detection, scalar-comparison, compact-coefficient
and structural hypotheses above are not proved by this assembly; supplying
them in the non-self-associated rank-one situation remains necessary for
the host task. The proof route reuses the imported constructions and
theorems, with no new original-literature assertion.

The 5 local instances have module-specific names to prevent generated-name
collisions when related modules are imported or replayed together. These are
the point-topology and affineness instances for `G` and, for each standard
index `J`, the Levi closed-immersion, affineness and point-topology instances
(`instRationalLocalInductionIrreducibility3` to `5`). As an anonymous instance,
the Levi point topology generated
`Langlands.Aubert.General.RationalPointFamily.instTopologicalSpaceRationalPointsLeviSchemeRootSet`.
`RationalLeviCuspidalRemainderTransport` generates the same name with a
different argument list. The instance types, bodies and local scope are
unchanged.
