# Principal open density on actual rational unramified characters

Author: Worker 34.

This is a derived consumer of the published actual unramified-character
coordinates and the polynomial torus-density unit. It introduces no new
representation-theoretic assertion and uses no original-literature claim beyond
the existing imported coordinate construction.

Let `F : Type u` be any nonarchimedean local field and `G` an actual connected
reductive group scheme over `F`. The assumptions and universe are those of
`rationalCanonicalUnramifiedCharacterCoordinates`. The rational-point topology
is exactly `rationalPointTopology F G.X`; affineness is derived from
`hG.isAffineHom`. The character space is the existing subgroup
`unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)` of
continuous complex-unit characters with its inherited compact-open topology.
There is no splitness, quasisplitness, characteristic-zero or positive-rank
assumption.

`rationalUnramifiedPrincipalOpen G hG p` is the preimage of
`complexTorusPrincipalOpen p` under the published coordinate homeomorphism
`rationalCanonicalUnramifiedCharacterCoordinates G hG`. The polynomial is
indexed by `Fin (rationalImageRank G)`, the actual valuation-image rank. The
membership theorem states exactly that evaluating the polynomial at the
underlying complex values of those coordinates is nonzero.

The principal open locus is open. If the polynomial is nonzero, the locus is
dense. Both claims follow by the general homeomorphism transport lemmas from
`CharacterTorusDensity`, applied to that actual coordinate homeomorphism.
Finite intersections agree with the locus of the product and are dense when
every selected polynomial is nonzero. The finite-family index has an independent
universe. Rank zero and the empty finite family are included. Finally,
`dense_of_rationalUnramifiedPrincipalOpen_subset` proves density of any family
containing one such nonzero principal open locus.

The project dependencies used by the proofs are exactly
`complexTorusPrincipalOpen`, its general openness, density, finite-product and
homeomorphism laws, and
`rationalCanonicalUnramifiedCharacterCoordinates`. The coordinate equivalence
retains its published actual valuation-image construction; no abstract substitute
for the actual character subgroup is introduced. No topology on a distribution
space is asserted.

A generic irreducibility theorem must still supply its nonzero polynomial and
prove that its required representation family contains this locus. This file
neither proves generic irreducibility nor equality of induced distributions.
Specialization to an actual standard Levi also requires the relevant group-scheme
and topology adapters; it does not assert reductivity of that Levi. The host
whole rational exact finite-length K0 Weyl-conjugacy proposition remains open.
