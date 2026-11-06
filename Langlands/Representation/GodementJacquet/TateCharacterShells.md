# Actual character shell coefficients

This internal unit computes character averages and eventual shell coefficients
for the actual multiplicative Haar measure normalized to give integral units
mass one. The field universe is arbitrary, and the topological data are supplied.
It does not assume local reciprocity or a correspondence.

A measurable subgroup average of a complex multiplicative character vanishes
when the character is nontrivial on that subgroup: left Haar invariance equates
the average with a nonidentity scalar times itself. This uses Mathlib's total
Bochner integral, so the cancellation lemma itself needs no integrability premise.
The indicator argument follows the shell cancellation technique in the published
`RamifiedFiniteFunctionMellinProof` (Worker 235), specialized here to a character
and exposed for a subgroup rather than a sufficiently ramified finite function.

The published shell decomposition identifies integral units with order zero.
The existing conductor-zero characterization therefore identifies triviality on
this actual subgroup. Its character average is one when the conductor is zero,
and zero otherwise.

`characterShellCoefficient` is the actual integral over integral units of
`Φ(π^n u) χ(π^n u)` for any specified order-one unit `π`. The published valuation
bounds for a Schwartz–Bruhat test make `Φ(π^n u)` equal to `Φ(0)` for all sufficiently
large `n`. Multiplicativity and the character-average computation give exactly
`Φ(0) χ(π)^n` in the conductor-zero case and zero in the conductor-nonzero case.

These are direct internal consequences of existing Haar, conductor, valuation
and Schwartz–Bruhat results. This unit does not yet identify the normalized
scalar or JPSS L-polynomial, supply a normalizing test, prove epsilon comparison,
or prove the closed all-field supercuspidal correspondence.
