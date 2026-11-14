# M144.069: signed powers of the deviation tend to zero

Worker 643 adapts Naganori Yamaguchi's
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1265–1285,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Copyright and author attribution remain in the header; Apache-2.0 LICENSE and
NOTICE remain in `licenses/NYLL/`.

The public theorem proves the exact U069 statement with the complete original
field, Galois, valuation-extension and local-field telescope and the original
containment and principal-unit-set membership hypotheses. M144.063 first places
the unit in `principalUnits L 1`; unfolding that membership and `pow_one` puts
its deviation from one in the maximal ideal of the valuation integer ring.

The private helper `signedPowersTendstoZeroForNormalBasis` supplies the
unpublished M132.017 input without reserving or duplicating its adapted public
name. It combines the source arguments of `PrincipalUnitQuotients.lean`, lines
162–199 and 247–268, from the same commit and registered source. Given a
zero-neighborhood in the integer ring, take an ambient valuation-ball
neighborhood and an irreducible uniformizer. An archimedean power bound makes
some uniformizer power smaller than the ball radius. Membership of the signed
powers in the corresponding maximal-ideal powers, followed by the ideal-power
valuation characterization, puts every sufficiently late signed power in the
neighborhood. This proves convergence to zero in the integer ring itself.

Dependencies are the unchanged U069 statement module, the M144.063 proof module,
and their transitive Library/Mathlib imports. The helper uses Mathlib's
`mem_nhds_subtype`, `IsValuativeTopology.hasBasis_nhds_zero`,
`IsDiscreteValuationRing.exists_irreducible`, `exists_pow_lt₀`,
`Valuation.integer.v_irreducible_lt_one`, `Ideal.pow_mem_pow`,
`Ideal.pow_le_pow_right`, and
`Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow`.
Namespace, imports and the explicit target application are adapted; the
unavailable source input is expanded into a private proof. No completeness or
inverse-closure conclusion is added to this target.
