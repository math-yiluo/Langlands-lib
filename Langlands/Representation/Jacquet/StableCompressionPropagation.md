# Fixed-exponent compact compression through sums and exact rows

Worker 1755, with interface and reuse guidance from Worker 1751. This is a
derived interface for the propagation step in Renard
2026 VI.9.3, printed p.200 / PDF p.206, using the stable-endomorphism exact-row
lemmas in Appendix C.II. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The fixed-vector direct-sum map is the actual componentwise inclusion and is
bijective: being fixed is a componentwise condition, and the inverse retains
finite support. `Langlands.fixedVectorsDirectSumMap` is this inclusion;
`fixedVectorsDirectSumEquiv` is the linear equivalence obtained from its
bijectivity. Their application lemmas identify each coordinate with the
underlying vector of the corresponding fixed-vector coordinate. The group,
index and component-carrier universes are independent.

The generic lemmas in `Langlands.LinearAlgebra.StableEndomorphism` use the
published definition
`Stable T := ker T = ker (T ^ 2) ∧ range T = range (T ^ 2)`.
`stable_of_equiv` and `stable_iff_of_equiv` transport stability through an
intertwining complex-linear equivalence. The forward direction applies the
published right-exact stability lemma to the zero map and the equivalence;
the reverse direction uses its inverse. `stable_directSum` proves stability
for the componentwise direct-sum map when every component is stable, by the
componentwise kernel and range formulas. `stable_directSum_iff` also proves
the converse, by including a vector into one summand and reading that
coordinate in the direct-sum stability equations.

In `Langlands.Jacquet`, `compressedAction_pow_natural_map` expresses the
published pointwise `compressedAction_pow_natural` as an equality of linear
maps, using extensionality. The pointwise law is imported from
`CanonicalLiftIntertwinerNaturalityProof`; it is not redeclared here.
Thus every power of the actual compressed action commutes with restricted
intertwiners. For an algebraically exact row of intertwiners
`A → B → C`, `fixedVectorsMap_range_eq_ker` proves equality of image and
kernel on compact-open fixed vectors: average a preimage in `A`, commute
averaging with the first intertwiner, and use that averaging fixes the
given vector in `B`.

`compressedAction_stablePower_of_rightExact` additionally assumes that
`B → C` is surjective and that the powers at exponent `b` are stable on
`A` and `B`; it proves stability of the power at the same `b` on `C`.
`compressedAction_stablePower_of_leftExact` instead assumes that `A → B`
is injective and that the powers at `b` are stable on `B` and `C`; it proves
stability at `b` on `A`. The published compact fixed-vector surjectivity
and injectivity results give the appropriate ends of the restricted rows.
The published C.II stable-row lemmas then apply to the three `b`-th powers,
using their naturality.

`compressedAction_pow_directSum` intertwines the componentwise `b`-th
compression powers with the `b`-th compression power of the actual direct-sum
representation under `fixedVectorsDirectSumEquiv`. Its proof applies power
naturality to every coordinate projection. Consequently,
`compressedAction_stablePower_directSum_iff` says that the power at `b`
on the direct sum is stable if and only if the power at the same `b` on
every summand is stable. These lemmas take a smoothness proof for each
summand and for the direct sum; for categorical smooth representations the
published `SmoothRep.directSum` supplies the latter proof.

There is no restriction on the index type, and the argument imposes no
dimension, admissibility or finite-length assumptions. All results hold
for every natural exponent, including zero. Positivity must be supplied
separately when using a stable power to deduce stationary power chains.

This module does not establish a stable power for an arbitrary smooth
representation. It supplies the propagation needed once representations with a
common stable exponent and their exact presentations are available. In
particular, it asserts neither the existence of such presentations nor a
representation-uniform exponent, and uses no dynamic-parabolic or contraction
hypotheses. Those are inputs to the remaining representation-theoretic
existence argument.
