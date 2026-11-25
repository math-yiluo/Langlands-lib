# Uniform right invariance of actual orbit constant terms

This internal derived module concerns the actual orbit coefficients and their
already defined chosen standard constant terms. It supports the compact-bound
input in Waldspurger (2003), Lemma VI.2.3, printed pp.299–301. The
registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The results are internal consequences of the existing coefficient, chosen
constant-term and orbit-topology interfaces.

`HasUniformStandardConstantTermRightInvariance` records a common open subgroup
of the actual standard Levi whose right translations fix every chosen
constant term in the family. Right invariance of the full function under a
compact open ambient subgroup passes to its constant term on the subgroup's
intersection with the Levi. The proof uses `standardConstantTerm_mul_right`
and triviality of the radical modulus on compact open subgroups. If the chosen
constant term's existence test fails, its defined value is zero and the
invariance statement remains valid. The generic inheritance lemmas retain the
maximal-split-torus and standard-cocharacter hypotheses of constant-term
uniqueness, the specified compatible component, and compact openness of the
right-invariance subgroup. They assume no constant-term existence target or
analytic coefficient bound.

The module specializes the generic bi-invariance and pointwise
parameter-continuity theorems to the actual rational induced orbit coefficients.
The shared compact open subgroup yields shared right invariance for the
actual `rationalOrbitConstantTerm` for every original field and independent
representation-carrier universe, under only the standard-cocharacter
uniqueness data. Pointwise parameter continuity of the full constant terms
then implies joint continuity by the common-open-subgroup lemma.

The final compact-bound corollary derives compactness of the full actual orbit
from the finite circle coordinates and quotient-orbit topology.
Joint continuity and the already proved continuity and positivity of the actual
Levi Xi then give `HasUniformWeightedCompactBounds` for the full actual
constant-term family. No additional orbit-compactness premise is assumed.

Pointwise continuity of the actual constant terms is an explicit premise of
the continuity and compact-bound corollaries; this module does not prove it, nor the final
positive-part decay theorem.
