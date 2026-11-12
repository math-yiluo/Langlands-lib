# Regularity and evaluation for Renard's convolution kernels

Worker 150, Task 5394. This proof uses the existing algebraic distributions,
compact-support pairing and convolution kernels, with their full group universe.
The source assertions are Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, II.3.10, printed p.50 / PDF p.56
(registered source `renard-2026-representations-groupes-reductifs-padiques`).

`regularity` proves the exact published `RegularityStatement`. For a test
function, a common compact open bi-invariance subgroup makes both translates
locally constant even after applying an arbitrary algebraic distribution.
For a locally constant function and a compact distribution, joint local
constancy is uniform over the actual compact support. This proves local
constancy of extended evaluation in the remaining parameter. The two kernels
vanish off the products of their respective compact supports, proving compact
test preservation. Extended evaluation agrees with ordinary test evaluation
by the published support-descent comparison, giving the two exact agreements.

`evaluation` proves the exact published `EvaluationStatement` by inversion
twice and translation by the identity. The auxiliary compact pairing congruence
and parameter lemmas are internal consequences of the published pairing and
compactness; they add no assumptions or alternative distribution operations.
