# From class pair gamma factors to actual generic actions

This internal adapter composes published factor and representation transport
results. It is a prerequisite for the associated-pair local induction argument.
It does not prove `AssociatedSupercuspidalInductionStatement`.

The intrinsic ordered L-polynomial relation quantifies over all compatible
quotient measures. Uniqueness of the normalized unipotent quotient measure
reduces each such measure to the canonical one. The canonical pair character
change theorem then proves that scaling the nontrivial additive character
preserves this intrinsic relation. Splitting into the two rank orders gives the
same conclusion for the symmetric relation, without changing the polynomial,
the actions or the additive measure.

For a generic pair, a classification L-polynomial supplies presenting tempered
Langlands data. The proved generic quotient L-factor theorem supplies one
polynomial common to their standard modules and the original actions.
Uniqueness for the standard-module pair identifies it with the supplied
classification polynomial. This proves the integral polynomial certificate
for the original actions at the same independent carrier universes.

For the actual smooth contragredient, standard-to-inverse Whittaker character
change and the smooth-dual Whittaker theorem supply a nonzero standard
functional for the original character. The resulting Whittaker type includes
admissibility. Irreducibility follows from admissible smooth duality and the
canonical compact-open cofinality theorem. Thus the actual contragredient of
each supplied generic action is generic for the same character.

The gamma adapter explicitly assumes
`GenericLanglandsPairEpsilonFactorComparisonStatement.{uF,uV,uW}`. It uses this
premise to turn the classification epsilon certificate into an integral
certificate for the supplied actions. The two proved L comparisons apply to
the actions and their actual smooth contragredients. Character change by
`-1` supplies the latter L certificate for the negated additive character;
the Gelfand--Kazhdan smooth-dual comparison turns it into the
inverse-transpose certificate required by `symmetricGammaExpression`.
That proved expression theorem yields the integral symmetric gamma
certificate for exactly
`rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P Pd`,
with the same self-dual additive measure.

For an automorphic class gamma certificate, its definition supplies original
and class-dual L certificates and the epsilon certificate. The class
smooth-dual relation identifies the dual classes with the contragredient
classes. The class L and epsilon representative equivalences then transport
all certificates to any supplied equivalent generic representatives in the
saturated carrier universes. Smooth-dual transport of the representative
equivalences handles the dual L certificates. Applying the preceding gamma
adapter preserves the supplied rational gamma function.

The theorem for the original automorphic object actions uses the proved
`SmoothRep.universeLift` and its actual representation equivalence. Genericity
transports to these saturated representatives, the class comparison applies,
and gamma invariance transports back to the original actions.
`HasGenericAutomorphicGammaComparison.{uF,uA} F` packages this conclusion for
every nontrivial character, its supplied self-dual measure, both positive
ranks, generic irreducible admissible objects and certified class gamma
function. The field and automorphic carrier universes remain independent.
The Rankin--Selberg helpers also retain independent pair-carrier universes.

`hasGenericAutomorphicGammaComparison` proves this internal proposition
conditional on the exact generic epsilon comparison at
`{uF,uA,uA}`. No unconditional epsilon comparison or associated-pair
gamma match is proved here. The original four-universe
`AssociatedSupercuspidalInductionStatement` remains a separate proof
obligation; this adapter adds no premise to that published statement.

The provenance is internal composition of the imported character-change,
generic quotient L-factor, Whittaker, smooth-dual, representative transport,
universe-lift and symmetric gamma expression results. The proof makes no
additional claim about the original literature.

The character-change equivalences reuse their existing `Langlands.RankinSelberg.Padic` counterparts in `AdjacentRankLargeTwistLDivisibility`; the dot-style adapters retain their input APIs.
