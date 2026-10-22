# Exactness from finite stages of continuous cohomology

Author: Worker 63.

`Langlands.Continuous.FiniteStageExactnessLimit` states a generic passage
from exact finite-stage sequences to actual continuous cohomology. The
coefficient ring `k` and group `G` lie in an arbitrary common universe.
The group is compact and locally compact, and `A` is the published genuine
continuous discrete module. Let `H` be an open normal subgroup and `q` a
natural cohomology degree.

The hypothesis ranges over every open normal subgroup `N` contained in
`H`. It asserts that the actual inflation

`H^q(G/H, A^H) → H^q(G/N, A^N)`

is injective and that its linear range is the kernel of the actual
finite-stage restriction

`H^q(G/N, A^N) → H^q(H/(H ∩ N), A^(H ∩ N))`.

The subgroup in the target is represented by pulling `N` back along the
subtype homomorphism of `H`; its coefficients are the corresponding
invariants of the restricted representation. All maps are the existing
`finiteInflation` and `finiteRestriction`, with no chosen replacements.

The conclusion states that `finiteStageToContinuous A H q` is injective
and its linear range is the kernel of `continuousRestriction A H q`, after
forgetting coefficient topology. Thus the continuous groups are Mathlib's
actual continuous-cochain homology, and the map from the finite stage is
the published canonical comparison map. It does not assert surjectivity
of restriction.

This is a derived, conditional limit lemma. Its finite-stage hypothesis is
an input to the general lemma and is not asserted for arbitrary modules.
In the intended algebraic-closure-unit application, finite Galois H2
exactness must separately prove that input. This statement neither proves
that finite exactness nor establishes the unconditional field-theoretic
`AbsoluteH2InflationExactness`. No vanishing hypothesis has been added to
that field-theoretic target.

The provenance is the direct-limit and continuous-cochain descriptions in
Serre, *Local Fields*, Greenberg translation (1979), X §3, printed p.154 /
PDF p.160, and the passage to the limit in X §4, Corollary to Proposition 6,
printed p.156 / PDF p.162. The registered source is
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 63 read PDF pages 160–162; no project errata entry was present.
Serre gives the Galois application; the arbitrary coefficient ring,
compact locally compact group, and conditional finite-stage formulation
here are an internal generalization. Its proof must use the published
actual finite-quotient comparison, subgroup cofinality and restriction
compatibility. This file only defines the proposition.
