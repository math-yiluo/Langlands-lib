# M144.071: inverse-correction products tend to one

Worker 643 adapts Naganori Yamaguchi's
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1309–1345,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original author/copyright header and Apache-2.0 LICENSE and NOTICE are
retained; the latter files are in `licenses/NYLL/`.

The public theorem proves the exact published U069 target, with the original
field, Galois, valuation-extension and local-field parameters and hypotheses.
For the deviation `x` of the unit from one, M144.069 says that the signed
successive powers tend to zero in the integer ring. Continuous subtype inclusion
transports that limit to `L`, and subtracting it from the constant one gives a
sequence tending to one.

A private finite geometric identity identifies this latter sequence term by term
with the products in the target. The helper
`normalBasisInverseCorrectionProductIdentity` expands the published
`inverseCorrectionPartialSum` by induction and `Finset.sum_range_succ`, then
applies Mathlib's `mul_neg_geom_sum`. It derives the needed unpublished M144.034
input under a private name, following the source's lines 569–601 (M144.032–.034)
from the same commit. This adds no second public adapted prerequisite theorem.
The relation `1 + x = u` and preservation of negation and powers by subtype
inclusion finish the identification.

Dependencies: unchanged U069 statement module, the M144.069 proof module
(and its M144.063 dependency), and `Mathlib.Algebra.Ring.GeomSum`.
The analytic steps use `continuous_subtype_val`, composition of limits,
`Tendsto.sub` and eventual equality. Namespace/imports and explicit target
application are adapted; the original limiting argument is retained, with the
finite geometric input expanded privately. This target claims the product limit,
without an inverse-closure or host reciprocity conclusion.
