# Multiplication for the canonical empty-index standard subgroups

Author: Worker 1623.

Let `G` be an affine connected reductive group scheme over any field `k`,
let `i : T → G` be an actual maximal split torus, and let `ν` be generic
for its actual relative roots. This module constructs
`Standard.emptyLeviMultiplicationIso`, an isomorphism of schemes over `k`
from the product of the existing canonical empty-index standard Levi and
unipotent representatives to the existing canonical standard parabolic
representative.

Its forward morphism is exactly
`subgroupMultiplication (Standard.leviToParabolic i ν ∅)
(Standard.unipotentToParabolic i ν ∅)`. The theorem
`Standard.emptyLeviMultiplicationIso_hom` records this identity. On every
test scheme, `Standard.comp_emptyLeviMultiplicationIso_hom` evaluates it
as the product of the two canonical images with the Levi factor first.
The construction is a scheme isomorphism, rather than only a bijection
on ground-field points. It makes no claim that multiplication is a
homomorphism from the direct product of group schemes.

The proof first combines the empty-index Levi comparison with
`genericCentralizer` to obtain the equality
`standardLevi i ν ∅ = Dynamic.centralizer (ν ≫ i)` on every test scheme.
The existing empty-index comparisons also identify the canonical
parabolic and unipotent subgroup functors with the dynamic functors of
the same cocharacter. Consequently the three canonical inclusion maps
represent the three dynamic functors. Their existing composition
identities identify the inclusions into the parabolic with the original
ambient inclusions. `Dynamic.isIso_subgroupMultiplication` then applies
directly to these actual maps. `asIso` packages that multiplication
morphism, and `comp_subgroupMultiplication` supplies the test-scheme
formula.

Provenance is derived from `MinimalStandardDynamicComparison`,
`GenericCentralizerProof`, `StandardRepresentability`, and
`LeviMultiplication`; no additional literature assertion is used.
The field universe is arbitrary, and no nonempty-root, positive-rank,
split-ambient-group, or additional finite-type hypothesis is imposed.

This construction supplies the multiplication clause needed for a
rational Levi. It does not prove connected reductivity of the canonical
Levi, geometric radical greatestness for the canonical unipotent group,
or geometric minimality of the parabolic. Those inputs, the remaining
split-torus assertions, compact subgroup existence and adelic coverage
are still needed for `AdelicGoodSiegelReductionStatement`.
