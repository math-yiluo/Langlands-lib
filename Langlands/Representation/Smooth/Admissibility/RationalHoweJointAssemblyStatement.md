# Rational Howe assembly using the joint basis's Levi representatives

`Langlands.SmoothRep.RationalHoweJointAssemblyStatement` is an internal
supporting implication with six explicit antecedents. Its conclusion is exactly
the published
`RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, uV}`:
finite group-algebra generation and admissibility imply finite length for every
smooth complex representation of the actual rational points of a connected
reductive group over a nonarchimedean local field, with the canonical topology.
The field/group and representation-carrier universes are independent. The
conclusion retains all field characteristics and includes the zero representation.

The antecedents are `GroupScheme.StandardCocharacterStatement`,
`GroupScheme.StandardLeviIntersectionStatement`,
`GroupScheme.RelativeRootSystemStatement`,
`BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`,
`Aubert.General.RationalPointFamily.RationalCuspidalCompactRestrictionStatement`
and `CuspidalSupport.RationalNormKernelFiniteRestrictionStatement`. The first
four have field universe `u`; the last two have field universe `u` and carrier
universe `max (u + 1) uV`, allowing the universe lift needed by the actual
cuspidal Jacquet subquotient theorem.

The compact-restriction premise concerns compact smooth-dual coefficients of
cuspidal representations on the actual common norm kernel. The finite-restriction
premise concerns every irreducible smooth complex representation: its
restriction is semisimple, has finite group-algebra length and admits a finite
spanning family of irreducible subrepresentations. The intended application
uses this general premise for a cuspidal Jacquet constituent.

This target strengthens `RationalHoweAssemblyStatement` by removing its separate
`StandardLeviSplitComponentStatement` antecedent. The intended assembly needs
that antecedent only for connected reductivity of the canonical standard Levi
scheme. The joint basis already supplies, for every relevant standard root
subset, an `IsCompatibleStandardSplitComponent` witness. Its definition contains
a connected reductive group scheme representing that same standard Levi
subgroup functor. The published
`SubgroupFunctor.IsRepresentedBy.isConnectedReductive` transport lemma is the
intended way to obtain connected reductivity of the canonical representative.
This describes an internal dependency route; this file states the implication
and contains no proof.

The intended assembly otherwise keeps the same ambient compact subgroup through
fixed-generator selection and Jacquet detection, uses intrinsic coefficient
data on the actual standard Levi and descends finite length along the universe
lift. No new translation of a literature assertion is claimed.

This statement proves none of its six antecedents and gives no unconditional
Howe theorem. It also does not prove the general all-field
`StandardLeviSplitComponentStatement`. The converse, separate VI.6.3
intermediate assertions and stronger compact-open length bound retain their own
obligations.
