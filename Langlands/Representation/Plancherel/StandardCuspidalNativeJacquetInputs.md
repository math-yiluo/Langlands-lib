# Native Jacquet inputs for standard cuspidal inducing objects

This internal adapter connects the published actual standard-family
cuspidality comparisons to the all-proper-rational-parabolic predicate in
`RationalSupercuspidalJacquetFamilyFiniteStatement`. It then constructs the
exact `RationalCuspidalNativeJacquetInputs` bundle used by the published
cuspidal-induction compression theorem. Its provenance is composition of the
named Library constructions; it claims no additional theorem from the
literature and does not prove either retained global representation-theoretic
statement.

`properRationalRadicalStandardization` accepts the original proper parabolic
map and its supplied geometric radical without a chosen Levi. The published
existence theorem chooses a rational Levi using the explicit
`ParabolicDynamicStatement` and the proved connected reductivity of dynamic
centralizers. If the parabolic map were an isomorphism, its all-test subgroup
range would be the whole group, contradicting the supplied properness.
The published `properParabolicUnipotentStandardization` then supplies a
proper finite standard face and a rational conjugating point identifying the
point subgroup of the original radical with the standard unipotent subgroup.
The original radical is retained. Maximal split-torus conjugacy, the actual
relative root system, a maximal split torus and its generic cocharacter
remain explicit inputs.

`properRationalJacquetVanishing_of_isCuspidal` applies that construction to
every test of `ProperRationalJacquetVanishing`. Standard cuspidality makes the
coinvariants at the resulting proper face subsingleton. The published
`coinvariantsTranslateEquiv` transports this conclusion to the original
radical's coinvariants. No normalization-character comparison is needed for
vanishing of the carrier.

`leviSchemeRepresentation_literalLeviRep` proves that the two canonical Levi
pullbacks recover the exact original representation on the same carrier,
using the inverse law of `parabolicLeviPointHomeomorph`.
`isSupercuspidal_literalLeviRep_of_isCuspidal` combines this equality with the
all-proper-rational vanishing comparison and smoothness of the literal
pullback. Thus its supercuspidality is the precise predicate used by the
native theorem, rather than a replacement condition on standard faces.

`rationalCuspidalNativeJacquetInputs_of_statements` takes
`RationalPointsIrreducibleAdmissibleStatement` and
`RationalSupercuspidalJacquetFamilyFiniteStatement` as premises. For each
irreducible standard-cuspidal inducing object it obtains admissibility from
the first statement, transports admissibility and irreducibility along the
actual Levi homeomorphism, and applies the second statement with the
supercuspidality just proved. The resulting bundle uses exactly the native
regular coefficient algebra and actual output Jacquet actions of the
published statement.

The field and carrier universes are independent. The cuspidality comparisons
work at the original carrier universe; the final bundle uses carrier universe
`max u uV`, as required by its existing definition. The represented ambient
root presentation, inducing semidirect decomposition, closed radical,
projection continuity, quotient compactness and geometric radical
identification are retained. This adapter supplies no exponent and does not
prove `UniformCompressionStabilizationStatement`; it identifies the precise
named inputs needed to use the existing compression reduction.
