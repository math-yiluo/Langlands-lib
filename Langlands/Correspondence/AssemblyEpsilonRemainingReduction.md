# Remaining premises for assembled epsilon inheritance

This internal module composes the published geometric reciprocity uniqueness
proof, arithmetic direct-sum proof, and earlier assembly reductions. Its
provenance is that composition of existing declarations; it asserts no new
external literature result.

`IsSupercuspidalCorrespondence.factorCompatibility_of_geometricReciprocity`
proves supercuspidal factor compatibility at any supplied geometric candidate
`e`. The proof extracts the candidate `e0` and system already witnessed by the
given supercuspidal correspondence. The published
`LocalClassField.geometricWeilReciprocityUniqueness`, applied at the canonical
topological datum, proves `e = e0`. Substitution gives the base relation for
`e`; the reciprocity family, local-constant assignment, system proof, and
pair-factor compatibility are reused unchanged. This theorem requires no
reciprocity existence or uniqueness premise.

`assemblyEpsilonInheritance_of_systemInheritance` applies the earlier
`assemblyEpsilonInheritance_of_geometricUniqueness_and_systemInheritance`
with that same published uniqueness theorem. Its only additional premise is
`AssemblyPairEpsilonSystemInheritance F`.

`AssemblyEpsilonRemainingReductionStatement.{uF, uP, uA} F` is the implication
from `MultisegmentHeadDatumMatching.{uF, uA} F` and
`SupercuspidalSegmentPairInheritance.{uF, uP, uA} F` to the unchanged
`AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F`. All three universes remain
independent.

`assemblyEpsilonInheritance_of_datumMatching_and_segmentPairs` proves this
implication. The fixed-system assembly reduction receives the two supplied
representation-theoretic premises. For every reciprocity family and supplied
system, the published `isArithmeticPairEpsilonFactor_directSum` proves
exactly its arithmetic direct-sum premise. The preceding assembly corollary
then supplies the original target. Thus reciprocity uniqueness and arithmetic
multiplicativity are proved inputs rather than additional assumptions.

The single system is still selected before the universal additive-character
quantifier, and the imported full compatibility conclusion retains existence
of a self-dual measure and compatibility for every such measure. The original
target and its hypotheses are unchanged.

This is a conditional supporting unit. It does not prove multisegment datum
matching or segment-pair inheritance, and does not supply an unconditional
proof of the host assembly target. Those two remaining premises must still
be discharged before that task can be completed.
