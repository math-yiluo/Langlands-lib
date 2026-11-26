# Convergence from actual opposite-radical level estimates

This module deduces `RationalUnipotentWeightIntegrabilityStatement.{u}`
from the two level estimates used in Waldspurger's proof of Lemma II.4.2,
formulated on actual rational points.

`rationalUnipotentWeightIntegrability_of_levelStatements` assumes exactly the
two propositions `RationalOppositeModulusLevelDataStatement.{u}` (the measurable
integer levels L with w = q^(-L/2) and the two-sided comparison of L log q with
1 + σ, from II.3.4) and `RationalOppositeLevelSetMeasureBoundStatement.{u}` (the
Haar bound C q^(n/2) n^d' on the level set {L = n} for n ≥ 1, II.4.1). It
applies both to the group, opposite subgroup U = `oppositeUnipotent i ζ`,
compact Iwasawa factor, representation and Haar measure quantified in the
target. The levels so obtained satisfy the hypotheses of the generic theorem
`unipotentWeightIntegrable_of_levelSets`. The other hypotheses are proved here:
the residue cardinality q is greater than one, the height σ is nonnegative, and
height sublevels in U have finite measure. No other estimate is assumed.

`measure_rationalHeight_sublevel_lt_top` proves that height sublevels have
finite measure, for any closed subgroup of G(F), any closed matrix
representation of nonzero size and any Haar measure on the subgroup. The
ambient height sublevels are compact by `isCompact_rationalHeight_le`. Their
preimages under the inclusion of a closed subgroup are compact, and a Haar
measure is finite on compact sets. The theorem is applied to U, which is
closed by `Aubert.General.RationalPointFamily.isClosed_oppositeUnipotent_localField`.

The generic theorem `UnipotentWeightIntegrable.exists_nat_exponent` replaces a
real exponent by a natural one. Choose a natural number n ≥ d. Since 1 + σ ≥ 1
and w ≥ 0, w (1 + σ)^(-n) ≤ w (1 + σ)^(-d), so the lower integral stays finite
by monotonicity. This step is needed because the generic convergence theorem
returns a real exponent and the target asks for a natural one.

The summation over level sets follows Waldspurger's proof of Lemma II.4.2,
printed p. 261, through the generic theorem above. The finiteness of height
sublevels for an arbitrary closed representation and the passage to a natural
exponent are internal deductions. They are needed because the target allows
an arbitrary compact Iwasawa factor and an arbitrary closed representation,
where the source works with its fixed special compact and embedding.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003). Registered as `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
PDF page = printed page minus 234.
