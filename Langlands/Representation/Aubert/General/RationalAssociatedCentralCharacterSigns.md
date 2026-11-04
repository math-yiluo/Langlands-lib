# Scalar characters under associated-Levi conjugation

This is an internal supporting construction for the rational rank-one
self-association argument. It constructs a full abstract center character
under actual associated-Levi conjugation and proves its value and logarithm
at the same common uniformizer. It does not prove the self-association
proposition or the Jacquet-module and admissibility inputs of that argument.

`scalarCharacter_eq_of_pullback_equiv` compares scalar characters under a
specified group equivalence and an actual representation equivalence with
its pullback. The groups and the two complex carriers have independent
universes. Only the source carrier is assumed nontrivial; no topology,
unitarity, admissibility or Schur hypothesis is required. The proof applies
the intertwiner to one nonzero vector and cancels scalar multiplication on
its nonzero image.

`standardCocharacterUniformizerCenter` evaluates a specified standard
cocharacter at the existing common field uniformizer and regards it as an
element of the actual full abstract Levi center. It uses the published
`leviCentralUniformizerSection` and `leviCentralTorusPointToCenter` maps.
Its ambient value is exactly `uniformizerPowers` of that cocharacter.

`associatedLeviCenterConjugationEquiv` is `Subgroup.centerCongr` of the
inverse of the published actual associated-Levi conjugation equivalence.
It maps the associated Levi center to the original Levi center by literal
conjugation by the supplied normalizer lift. The rational construction
retains connected reductivity, maximal splitness, genericity, the standard
Levi conjugation statement, actual normalizer and centralizer comparisons,
the actual Coxeter system, root-length and positive-reflection comparisons,
minimality and associated-subset laws. The simple-root and Weyl types are
finite, and the point group has its specified topological-group structure.
For the uniformizer conclusions there is additionally a relative root
system and a specified standard cocharacter. The affine and monomorphism
instances are explicit in the Lean context. These are structural inputs;
no representation-theoretic or sign conclusion is assumed.

`associatedLeviCentralCharacter` composes an arbitrary full original-center
character with this precise center equivalence, for every index and every
lift representing its specified longest class. The generic scalar comparison
specializes to `scalarCharacter_eq_associatedLeviCentralCharacter`: whenever
an actual associated-Levi representation is equivalent to the specified
pullback of the original representation, their scalar characters agree
with this construction. Its nontrivial source-carrier assumption remains
explicit, and no valuation or local-field hypothesis is used in this
scalar comparison.

The center equivalence sends the point of
`associatedOppositeStandardCocharacter` to the inverse original point.
The proof compares the underlying ambient points and applies
`uniformizerPowers_associatedOpposite_conj`; thus the longest lift and the
common uniformizer are unchanged throughout. Applying the original character
and its inverse law proves
`associatedLeviCentralCharacter_standardUniformizer`.

`Langlands.Plancherel.normLog_inv` follows from the published product and
unit formulas for the residue-normalized norm logarithm, for any real base.
Applying the norm map on complex units to the character-value identity and
then this inverse formula gives
`associatedLeviCentralCharacter_latticeLog`. Its two lattice logarithms use
the original standard cocharacter and its actual associated-opposite image,
respectively. The conclusion is equality with the negative original
logarithm. This does not assert that both real slopes have equal magnitude,
or supply their sign alternatives on all torus tests.

All constructions and proofs here are derived from the named published
transport maps, elementary equivariance, scalar cancellation and group
homomorphism laws. No external literature assertion or new axiom is used.
