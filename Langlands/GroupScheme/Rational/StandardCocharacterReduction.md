# Standard-cocharacter comparison reduction

Worker 185, using Worker 163's positive-root and sign helpers. This internal
reduction combines the published pointwise-intersection definitions with the
split-lattice construction and relative-root combinatorics. It retains the
universe, arbitrary field, and all test schemes of the existing interfaces.

`StandardCocharacterDynamicComparison i ν J` says that any two standard
cocharacters for the same face give equal dynamic parabolic, centralizer,
and unipotent subgroup functors. It does not assert that a standard
cocharacter exists. Its equivalence with agreement of the three standard
intersections with every standard cocharacter is proved directly. One
inclusion follows from membership in an intersection. For the reverse
inclusion, transport membership along the assumed equality to each member
of the intersected family. Conversely, two dynamic subgroups agree because
each equals the same standard intersection. These are equalities of subgroup
functors on every test scheme.

`HasRelativeRootSystem.standardCocharacters_haveSameRelativeRootSigns`
uses actual-root negation closure from the explicit relative-root-system
realization and splitness, then applies Worker 163's sign theorem to two
standard cocharacters. Genericity is assumed for the fixed cocharacter.
`HasRelativeRootSystem.standardCocharacterDynamicComparison` additionally
assumes the sign-to-dynamic comparison and applies it to this sign equality.
It supplies no proof of that structural comparison.

`exists_standardCocharacter_of_relativeRootSystemStatement` applies the
existing conditional existence theorem to the realization supplied by an
explicit proof of the general `RelativeRootSystemStatement`. This isolates
the existence conclusion from all dynamic comparisons. Splitness and the
monomorphism instance come from maximal splitness, and the affine instance
comes from connected reductivity.

`standardCocharacterStatement_of_relativeRootSystem_of_signs` combines these
steps. Its conclusion is exactly the published `StandardCocharacterStatement`
at universe `u`, and its hypotheses are the published propositions
`RelativeRootSystemStatement.{u}` and
`RelativeRootSignsDetermineDynamicStatement.{u}`. Both quantify over every
connected reductive group with maximal split torus. The former constructs a
standard cocharacter and proves root negation closure; the latter identifies
all three dynamic subgroups for cocharacters with the same relative-root
signs. The explicit sign formula in the latter is definitionally equal to
`HaveSameRelativeRootSigns`, so the proof applies it directly without an
additional comparison premise or an alternate sign statement. The intersection
argument then gives the three required equalities for every standard cocharacter.

This is an intermediate conditional reduction. It does not prove the general
relative-root-system theorem, the sign-to-dynamic comparison, or the
unconditional `StandardCocharacterStatement`. Neither structural input is
introduced as an axiom. The empty root set and every actual subset are
included, with no reducedness or characteristic restriction.
