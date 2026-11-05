# Proof of the corrected logarithmic comparison

Worker 6 supplied the proof draft; Worker 1593 verified and prepared this pair
for submission.

This proof targets
`Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedLogarithmicComparisonStatement`.
Its statement companion supplies the exact derived provenance from Renard
V.3.20 and VII.2.1, including the correction by `-log q`. This proof uses the
published real split-torus constructions rather than constructing the source's
full complex exponential map.

The original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are V.3.14–V.3.15, printed p.113/PDF p.119;
V.3.19–V.3.20, printed pp.115–116/PDF pp.121–122; VII.1.1, printed
p.220/PDF p.226; and VII.2.1, printed p.227/PDF p.233. The theorem is
a derived comparison under the published positive valuation and `q^(-s)`
normalization. The source's later raw-log formula differs by `-log q`;
this theorem proves the corrected comparison specified by its statement.

For each specified actual exponent, the proof extracts its open character
kernel from `isNormalizedJacquetExponent_iff_isOpen_ker_and`. The
split-component witness supplies affineness; its canonical point topology
is the topology used by `SplitTorusNormFormula`.
The published all-point raw pairing formula, followed by
`rawLogRealPart = (-log q) • normalizedRealPart`, gives the corrected
logarithmic equation for the constructed normalized parameter.
This parameter witnesses the forward cone-test implication.

For the reverse implication, a parameter satisfying that equation has the
same pairings with every actual valuation vector as the constructed one:
cancel the nonzero factor `-log q` from their logarithmic equations.
`eq_of_pair_valuation_eq` identifies the two parameters. Thus membership
in the specified presentation's cone transfers to the normalized parameter.

The negative raw parameter is `log q` times the normalized parameter.
Positivity of `log q`, which follows from `q > 1`, and positive scalar
closure of `pres.nonnegCone` prove the forward sign comparison.
Scaling by the nonnegative inverse of `log q` proves the reverse comparison.
Both use the same full-space cone for the same actual presentation.

Finally the proof unfolds the all-parabolic predicate in both directions,
preserves admissibility and each `Nonempty` presentation conjunct, and applies
the first local equivalence to every presentation, matching represented
radical/decomposition and exponent. It proves no presentation-existence
theorem. Independent field/group universe `u` and representation universe `v`,
the canonical topology, and all other statement hypotheses are retained.
The full complex lift, surjectivity and period-lattice assertions, structural
choice independence and the separate temperedness consequences remain outside
this theorem. Global presentation existence and transport, standard
reduction, full-group and central-character consequences, Casselman’s
implication, and classification retain their separate proof obligations.
No irreducibility, central-character, nonzero-carrier or finite-dimensional
carrier assumption is added.
