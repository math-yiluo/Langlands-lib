# Modulus cases for actual associated maximal Levi characters

This is an internal consequence of the actual Levi-central logarithm and
associated-character constructions. It constructs logarithmic modulus data
and proves paired modulus alternatives. The exact
`RationalRankOneSelfAssociationStatement` remains open.

`MaximalLeviCentralCharacterLogData` retains an actual simple-root index `I`
and a character of the full abstract center of `levi i ν I`. Its fields are
an omitted simple root, an equality of the original index with the complement
of that root, a real slope, and the logarithmic factorization on every actual
Levi-central torus point. The factor uses the integral order of the omitted
simple root, with the sign convention of `Plancherel.fieldOrderUnits`.
The ambient group is affine, the field is a nonarchimedean local field of
arbitrary universe `u`, and the actual simple-root type has finite and
decidable equality instances.

`maximalLeviCentralCharacterLogData` constructs this data for every maximal
proper index and every full-center character with open kernel and unit
modulus on the actual ambient center. It chooses the omitted root and uses
`exists_leviCentralTorusCharacterLog_factor_of_rationalData` for the real
slope and factorization. Its explicit inputs are the actual point normalizer
and centralizer comparisons, Coxeter system, standard-cocharacter statement,
connected reductivity, maximal split torus, relative root system, generic
cocharacter, root-length comparison and actual Levi-Weyl identification.
The topology is the actual rational-point topology, with the displayed
affine-torus, topological-group, Hausdorff and monomorphism instances.
The ambient-center restriction uses `ambientCenterToLeviCenter` and the
proved inclusion `center_le_standardLevi`.

`standardCocharacterUniformizer_isNoncentralNegative` proves that the actual
uniformizer point of every standard cocharacter for a maximal proper index
is a noncentral negative torus point. Standardness gives zero pairings on
the selected simple roots and strictly positive pairings on the other roots.
The omitted root supplies the required strict pairing. The published
`isNoncentralNegativeTorusPoint_uniformizerSection` converts these pairings
to the original strict valuation chamber using the common field uniformizer.
This result does not assume the existence of a noncentral test separately.

`MaximalLeviCentralCharacterLogData.norm_trichotomy` applies the factored
logarithm trichotomy to the chosen omitted root and transports it back to the
original index. It concludes that the character has norm strictly below one
on every noncentral negative central-torus test, has norm strictly above one
on every such test, or has norm one on every central-torus point. The
omitted-root chamber comparison supplies the strict order needed in the
first two cases. The point-to-center identification ensures that the
conclusion concerns the literal full-center element supplied in the test.

`associatedLeviCentralCharacters_norm_cases_of_logData` considers two such
characters, on `I` and `associatedSubset cs I`, whose equality under the
specified actual longest conjugation is explicit. It also assumes the
standard-Levi conjugation statement, positive simple-reflection comparison,
minimality-length criterion, associated-subset laws and finite actual Weyl
group. These are structural premises, with no assumption about the signs
of either character. Its conclusion is the disjunction:

- The first character has norm below one on every noncentral negative
  central-torus test for `I`.
- The second character has norm below one on every such test for the
  associated index.
- Both characters have norm one on all their respective central-torus
  points, without a chamber restriction.

The proof chooses a standard cocharacter for `I` using the supplied
standard-cocharacter statement, then applies the actual
associated-opposite standard-cocharacter map. Both resulting uniformizer
points are strict tests by the preceding lemma. The published
`associatedLeviCentralCharacter_standardUniformizer` identifies the two
character values as inverses. Applying the individual trichotomy first to
the original character and then to the associated character proves the
three alternatives: a norm above one on the first test forces a norm below
one on the second, while a unit value on the first forces a unit value on
the second. The strict alternatives in the second trichotomy therefore
exclude its incompatible branches.

`associatedLeviCentralCharacters_norm_cases_of_rationalData` constructs both
logarithmic data objects and gives the same conclusion directly from maximality,
open kernels, ambient-center unit modulus and the actual character-transport
equality. Associated-subset cardinality preservation proves maximality of the
second index; its maximality is not an additional premise. The character
equality can in turn be supplied by
`scalarCharacter_eq_associatedLeviCentralCharacter` from an actual
representation equivalence and its two scalar-action identities.

The derivation reuses published Lean results and makes no new literature
claim. This unit does not construct the needed Jacquet equivalence, prove
admissibility, extend unit modulus to the entire abstract Levi center, or
prove irreducibility of induction. Those steps are still required in the
self-association argument.
