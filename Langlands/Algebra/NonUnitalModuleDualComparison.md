# Nondegenerate dual comparison under double-opposite transport

Worker 1149 completes and extends Worker 6's feasibility construction. This is a
derived internal comparison supporting the two dual functors of Renard I.4.1,
printed pages 22–23 / PDF pages 28–29. The governing source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version 9 July 2026,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original nonunital conventions are on printed pages 5–7 / PDF pages 11–13;
the canonical complex scalars are I.2.1, printed page 14 / PDF page 20.
The registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, changes no construction here; its nonzero-vector correction
concerns the later injectivity argument. The 2026 edition governs.


All declarations are in `Langlands.Algebra.NonUnitalModuleDualComparison`.
`dualComparison` restricts the imported full-dual equivalence to the actual
nondegenerate subtypes. A raw fixing idempotent in the triple opposite is
transported to the target A-opposite algebra through two `unop` operations;
the inverse uses two `op` operations. Idempotence follows by applying the same
operations to the original idempotence equation. The fixing equations are
verified by evaluating the full functionals. This uses no extra comparison
witness and makes no finiteness or nonzero assumption.

`dualComparison_val` and `dualComparison_symm_val` identify the entire included
full functional with the forward and inverse full-dual comparisons.
The corresponding `*_val_coe` laws identify the entire functions.
`dualComparisonHom` and `dualComparisonInvHom` bundle precisely these additive
maps as original A-opposite intertwiners, with the source action explicitly
transported from the triple opposite. The two `dualComparison_inverse_*`
laws equate their complete composite intertwiners to identities. The
`*_toAddMonoidHom` laws expose the complete additive-map agreements.

`dualComparisonLinear` packages the same equivalence for the two explicitly
inherited `dualModule` structures. Scalar linearity follows by subtype and
functional extensionality from pointwise scalar multiplication.
`comparisonSourceModule` names the canonical module recovered from the
transported original source action. `comparisonTargetModule` names the
canonical module recovered from the target original action. Their
`*_eq_dualModule` laws prove equality of each complete module with its inherited
pointwise module, using the imported scalar-transport equality and the published
canonical/inherited module equality. `dualComparisonCanonicalLinear` uses
these exact recovered modules. It agrees with the original intertwiner as an
entire additive map and with its automatic `complexToLinearMap` as an entire
linear map.

`dualComparison_cross_naturality` compares pullback for an arbitrary original
double-opposite intertwiner M to N, at independent carrier universes. The raw
pullback is transported after dualizing; the other pullback first transports
the original map and then dualizes. Both paths agree as entire original
A-opposite intertwiners. `dualComparison_linear_naturality` states the same
square as equality of entire complex-linear maps with the exact recovered
modules. Both proofs use map extensionality followed by subtype and functional
extensionality: both sides evaluate to the same original functional at f(m).

The paired Checks module assigns complete unapplied interfaces, including the
two naturality laws, at independent algebra, source and target universes and
at explicit unequal universe specializations. All competing actions and modules
appear in the expected types. This is a derived internal comparison for the
source dual functors; the actual right categorical bidual and transported
source evaluation are separate constructions. No injectivity, reflexivity,
exactness or later fixed-part duality is claimed.
