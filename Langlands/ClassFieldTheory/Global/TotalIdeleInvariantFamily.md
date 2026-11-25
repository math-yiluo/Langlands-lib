# The total invariant family on actual idele cohomology

This derived supporting construction packages the published local sums as an
`IdeleInvariantMaps` family in any common universe. Its source is Artin–Tate,
*Class Field Theory* (2009), Chapter VII §3: the sum of local invariants on
printed pp.43–44, reciprocity in Theorem 6 on pp.45–47, Remark 1 on pp.47–48,
and the cyclic prime-power argument in Lemma 5 on p.49. The arithmetic results
needed from that argument remain explicit hypotheses.

`totalIdeleInvariantMaps` uses the existing `placeAbove E` at each finite base
place and the published canonical archimedean sum. It takes the supplied local
family `I` and its `RelativeImages` proofs. It agrees with `totalIdeleInvariant`
for every choice of infinite places and those fixed finite choices. The proof
uses the published independence of the archimedean sum. A private choice of
infinite lifts, obtained from surjectivity of the map on infinite places, lets
the remaining proofs apply the existing theorems about the explicit total sum.

Every value lies in the denominator subgroup for the global extension degree.
For a local section at a chosen finite place, the value equals the supplied
local invariant. The corresponding theorem keeps explicit the finite coset
type used to construct that section.

Assuming `CyclicPrimePowerLocalDegreeStatement`, the family satisfies the
`CyclicRange` condition required by the regular-class assembly. This applies
the published coverage theorem to the chosen finite lifts and then the theorem
giving the full range of the total invariant. No place of full global degree
is assumed.

Assuming `GlobalReciprocity` and the supplied family's relative class formation
and arithmetic normalization, the family satisfies `KillsQuotientKernel`.
The proof uses the actual coefficient exact sequence through the published
kernel-vanishing theorem for the total sum. A second theorem supplies
`GlobalReciprocity` from the published `globalReciprocity_of`, leaving
`IdeleClassH1Vanishing` as an explicit input.

This module does not prove the prime-power local-degree statement or `H¹`
vanishing. It does not establish independence of finite-place choices,
inflation or restriction compatibility of this family, or the finite-place
compatibility condition on global idele-class invariants. In particular it
does not prove `GlobalInvariantStatement`.
