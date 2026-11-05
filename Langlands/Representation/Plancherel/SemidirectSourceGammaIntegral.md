# Regularity and real integration of the source gamma integrand

Worker 200. This is a derived consumer of `SemidirectSourceGamma` and the
existing `HarishChandraSchwartz.Spherical` weight. It does not replace their
objects or assume continuity of chosen Iwasawa components.

Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, I.1 (2), (3), printed pp.240–241 / PDF pp.6–7, fixes Haar
mass one on intersections with the special compact subgroup, writes
`G = P K`, and defines `gamma(P)` by the opposite-radical integral of
`delta_P(m_P(v))`. The original is registered as
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The regularity and real-integral comparisons below are internal consequences
for the actual subgroup interfaces, rather than additional numbered source
theorems.

The group universe is arbitrary. The ambient group is nonarchimedean and
locally compact. The data are an actual semidirect
decomposition `P = M U`, its continuous projection, a closed radical `U`,
an open subgroup `K`, and an actual `G = P K` factorization. The source
Levi modulus is the existing closed-subgroup Haar character for conjugation
on `U`. `sourceIwasawaModulus` evaluates that character on the Levi
coordinate of the already constructed chosen parabolic factor. It is a
strictly positive real function. `sourceIwasawaPair` merely expresses the
same factorization in the existing spherical-weight interface.

For regularity, `P` is closed and `K` is compact. The Levi modulus pulled back through
the actual projection has open kernel. Its restriction to the compact
subgroup `P ∩ K` is trivial by the existing finite-index, torsion-free
positive-character argument. `sourceIwasawaModulus_eq_weight_sq` identifies
the actual scalar function with the square of the existing Iwasawa
weight. That weight is independent of its factorization and locally
constant for open `K`. Squaring proves local constancy and continuity of
the scalar modulus, without any regularity assertion about its chosen
Levi or radical components.

`semidirectSourceGammaReal` is the real value of the exact original
nonnegative open-cell constant. Under the earlier source compact
splitting and mass-one hypotheses, right invariance of the two factor
Haar measures, and inversion invariance of the opposite measure, the
earlier Iwasawa lower integral is exactly the lower integral of
`ENNReal.ofReal sourceIwasawaModulus`.

The real integrability and positivity results retain the original
open-cell hypotheses: local compactness and second countability of `P`
and the opposite subgroup `V`, an ambient right-invariant Haar measure,
Haar measure on `V`, actual open embedding, and an ambient Haar-null
complement. They also retain the preceding factor Haar, countability
and normalization assumptions. Scalar continuity gives strong
measurability on `V`; the already proved finiteness of the same
open-cell constant gives finite norm integral. This proves genuine
Bochner integrability. The nonnegative real integral is the real value
of that lower integral, hence equals `semidirectSourceGammaReal`.
Nonzero and finite lower gamma give strict positivity of its real value.
There is no change of Haar scale.

The actual rational open-cell conullness assertion remains a separate
unproved target. Source compact factorization and normalization, the
comparison with each rational parabolic, independence of gamma from
the parabolic with fixed Levi, root-index products, `c(G|M)`, spectral
density and the Plancherel formula remain separate obligations. No
induced irreducibility, analytic-chart conclusion, integral convergence
or chosen-component continuity is supplied as a substitute for a proof.
