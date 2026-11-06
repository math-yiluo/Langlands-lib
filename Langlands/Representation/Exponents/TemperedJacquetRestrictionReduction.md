# The exact unitary restriction target reduced to Jacquet admissibility

Author: Worker 1629.

This derived reduction assembles existing constructions for Renard 2026,
VII.2.3 and VII.2.4, printed p.229 / PDF p.235. It provides two conditional
routes to the unchanged `TemperedJacquetUnitaryRestrictionStatement`.

`TemperedJacquetUnitaryRestrictionReductionStatement` states that the
published `ArbitraryParabolicJacquetAdmissibilityStatement` implies that
restriction target. Its proof extracts ambient admissibility from the
given normalized-exponent temperedness of the source. The assumed
admissibility-preservation statement then gives admissibility of the
actual normalized Jacquet module. The published splitting theorem
`unitaryJacquetPart_isCompl_nonunitaryJacquetPart_of_admissible` gives
complementarity of its two actual parts. Finally,
`leviUnitaryJacquetRestriction_bijective_of_isCompl` gives bijectivity of
precomposition with the literal `leviUnitaryJacquetModuleι` into the
tempered target.

The second theorem,
`temperedJacquetUnitaryRestriction_of_unitaryJacquetPartTempered`,
instead assumes the exact published VII.2.3 statement. It takes that
statement's complementarity clause and applies the same bijectivity
lemma. The temperedness clause for the unitary part is not needed.

Both proofs introduce every quantifier of the existing target, retaining
independent field and carrier universes, the local-field and topology
hypotheses, all actual parabolic, Levi, radical and split-component data,
and the canonical locally compact nonarchimedean Levi-point topology.
They reuse the existing restriction equivalence and its extension by zero;
they define no replacement Jacquet objects or maps.

The first route assumes general Jacquet admissibility preservation, and
the second assumes VII.2.3. Neither assumption is proved here. These
conditional implications do not constitute an unconditional proof of
VII.2.4 or completion of any of the three host-task targets. Their
provenance is the composition of the existing splitting and restriction
constructions, rather than a separate assertion quoted from the source.
