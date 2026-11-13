# Rational contragredient commutation from the remaining representation inputs

Author: Worker 3919. This is an internal composition of published proofs. It
proves a conditional implication, not the closed
`RationalContragredientCommutationStatement`.

`RationalContragredientAssemblyStatement.{u,v}` states that these three
representation-theoretic propositions imply the original commutation target:

1. `RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v}`;
2. `DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v}`;
3. `RationalInducedClassWeylConjugacyStatement.{u,v}`.

The first two supply admissibility when the actual natural duality
isomorphisms are evaluated at finite-length ambient or Levi objects. The
third supplies equality of actual normalized induced classes under the
stated normalizer conjugation. None of the three is proved in this module.
In particular, smooth-dual finite-length preservation alone does not supply
these comparisons.

`rationalContragredientCommutation_of_admissibility_and_inducedWeyl` proves
the displayed implication. It introduces its three antecedents and applies
the published `rationalContragredientCommutation_of_schemeWeylDuality`.
Five of that reduction's eight inputs are now supplied by actual published
proofs, as follows:

| Input | Published proof supplied |
| --- | --- |
| `RelativeWeylCoxeterStatement` | `Langlands.GroupScheme.relativeWeylCoxeter` |
| `StandardLeviConjugationStatement` | `Langlands.GroupScheme.standardLeviConjugation` |
| `StandardAssociatedOppositeTransportStatement` | `Langlands.GroupScheme.standardAssociatedOppositeTransport` |
| `RationalNaturalInductionDualityStatement` | `rationalNaturalInductionDuality` |
| `RationalNaturalJacquetDualityStatement` | `rationalNaturalJacquetDuality` |

The other inputs are exactly the three antecedents above. No additional
structural or representation proposition is assumed in this implication.
This assembly leaves the original target and its imports unchanged.

The applied reduction chooses the actual finite relative-Weyl Coxeter system,
the cardinality-preserving `associatedSubsetEquiv`, and actual longest
normalizer lifts. Its standard/opposite subgroup membership identities come
from `associatedOpposite_mem_of_structural`. The generic theorem
`contragredientTermComparison_of_duality_of_weylConjugacy` transfers Jacquet
finite length through `jacquetConjugationIso` and obtains opposite/standard
induced-class equality through
`conjugateInductionClass_eq_of_weylConjugacy`. The actual duality components
are `finiteLengthJacquetDualityIso` and `finiteLengthInductionDualityIso`;
their natural families are supplied by the published duality proofs above.
Finally, `contragredientCommutation_of_termComparison` rewrites the signed
sums on actual representation classes and applies
`FiniteLengthGrothendieckGroup.hom_ext_object`. Thus the conclusion concerns
the whole exact finite-length Grothendieck group, with all its actual
short-exact-sequence relations.

Every scope condition is inherited literally from the unchanged target:
independent universes `u` and `v`, carriers in `max (u + 1) v`, every
nonarchimedean local field including positive characteristic, every connected
reductive group including nonsplit and non-quasisplit groups, the maximal
split torus and generic cocharacter, canonical `pointTopology`, actual
standard subgroup families, and literal `SimpleRoot i ν` labels including
the empty type. Ambient induction and Jacquet finite length and ambient
smooth-dual finite length remain the target's separate premises. Compact-open
cofinality is still derived by `compactOpenCofinal_of_nonarchimedean`.
The coefficients remain `(-1)^|I|`, because the associated-subset equivalence
preserves cardinality.

The composition itself uses no Langlands classification, character
independence, geometric lemma, adjointness or cuspidal-support theorem.
The generic reduction's finite-length reflection uses the lattice transport
`FiniteLengthAssembly.finiteLength_comp_surjective_iff`, through
`FiniteLengthAssembly.length_comp_surjective` and
`CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`. The last is
an order equivalence under a surjective acting-group map, not a
cuspidal-support assertion. The imported natural Jacquet-duality proof uses
the stable pairing from a contracting element and opposite Iwahori basis.
The imported induction-duality proof uses compactness of the parabolic
quotient and the Haar modulus comparison. The structural proofs concern
actual algebraic groups and their relative roots. The paired Markdown of
these published proofs records their implemented arguments.

Any future proofs of the three explicit antecedents require their own
dependency audit. In particular, using an induced-class Weyl proof obtained
through distribution characters would add that proof's character-independence
dependencies to the final closed commutation theorem. This implication does
not claim those antecedents are classification-independent or already
proved. Aubert Proposition 3.2 is not used.

The provenance is internal: the new proposition records the result of
composing the named Library proofs with an existing reduction. It makes no
additional original-literature assertion and does not discharge Task 3919's
requirement to prove the original unapplied proposition.
