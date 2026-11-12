# Compact open fixed spaces of actual unramified parabolic inductions

This internal construction compares the fixed spaces of the actual normalized
inductions of two inertia-related actions of one fixed standard Levi scheme.
It is a supporting result for the fixed-vector category problem. It does not
prove visibility of all irreducible constituents of an induction.

The generic `Induction.compactTrivialTwistInducedFixedVectorsEquiv` assumes a
closed subgroup `P` with compact left quotient, a compact open subgroup `K`,
an arbitrary complex representation of `P`, and a character of `P` trivial on
each compact subgroup. Choose a finite double-coset transversal by the
published `exists_finset_doubleCoset_representatives`. Evaluation identifies
the twisted and untwisted induced fixed spaces with the same product of
coefficient fixed spaces. The comparison composes `fixedTwistEvaluationEquiv`
with the inverse `fixedEvaluationEquiv`. Closedness of `P` makes each
conjugate stabilizer compact. No smoothness or admissibility assumption on
the inducing representation is needed for this comparison of smooth inductions.

`Aubert.General.normalizedInductionCompactTrivialTwistFixedVectorsEquiv`
packages the same comparison for a semidirect parabolic decomposition. The
ambient group is locally compact and nonarchimedean, the unipotent subgroup is
closed, and the inducing parabolic is closed with compact left quotient. The
Levi character has open kernel, and its inflation is assumed trivial on compact
subgroups of the parabolic. The published `inducingRepresentation_twist`
commutes the twist with half-modulus normalization; the generic induced-space
comparison then applies.

The rational specialization works over an arbitrary nonarchimedean local
field `F` in universe `uF`, on the canonical topology of the actual rational
points of an affine locally finite-type group scheme, with the stated local
compactness and nonarchimedean instances. Ambient finite type is an explicit
typeclass hypothesis, already supplied by connected reductivity through
`BernsteinStandardFamily.locallyOfFiniteType`. Closed immersion of each standard
Levi supplies its affineness and finite type. `family` is the published actual
`BernsteinStandardFamily`: connected reductivity, a maximal split torus,
a generic cocharacter and the structural standard subgroup decompositions.
The representation carriers belong to the independent universe `uV`;
induction has carrier universe `max uF uV`.

`rationalStandardInduction` applies the published normalized induction functor
to an arbitrary smooth action of the represented standard Levi scheme, after
pullback through the inverse canonical Levi point homeomorphism. For a
cuspidal datum `a`, this is definitionally the existing `bernsteinInduction a`.

`rationalUnramifiedInductionFixedVectorsEquiv` compares this induction for a
full actual rational unramified twist with the induction of the original
action, at any specified compact open `K`. The twist character on the inducing
parabolic is the character on the Levi scheme composed with the inverse point
homeomorphism and the actual Levi projection. Both maps are continuous.
The published `compactSubgroup_le_unramifiedPullback_ker` makes that character
trivial on compact subgroups, using continuity of every actual rational norm
character. The half-modulus normalization commutes with the character twist
by the generic normalized comparison. Pullback of the rational character to
the literal Levi has open kernel by continuity of the point homeomorphism.

Closedness of the standard parabolic, continuity of its projection and
compactness of its left quotient are discharged with published structural
theorems. Compactness uses the unconditional
`BruhatTits.dynamicParabolicQuotientCompact`, transported through the
unconditional standard-cocharacter theorem. No additional quotient compactness
or projection-continuity premise is imposed in the rational specialization.

`rationalInertiaInductionFixedVectorsEquiv` chooses the full unramified
character and actual isomorphism in `IsRationalInertiaRelated`, applies the
twist comparison, and then transports the actual isomorphism through the
Levi pullback and normalized induction functors. The final theorem transfers
nontriviality of the compact open fixed space. These results assume no
cuspidality, irreducibility, admissibility or finite length of either action.

The provenance is a derived construction from the named published fixed-vector,
compact-stabilizer and actual rational standard-parabolic interfaces. It does
not compare distinct embedded Levis under ambient conjugation, nor establish
generation at the prescribed `K`, fixed-vector visibility of every constituent,
a Bernstein decomposition or `FixedVectorCategoryStatements`.
