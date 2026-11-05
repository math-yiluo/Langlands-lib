# A normal unipotent envelope for a subgroup contained in every Borel

`Langlands.GroupScheme.unipotentAllBorelsEnvelope` proves exactly
`Langlands.GroupScheme.UnipotentAllBorelsEnvelopeStatement.{u}` at arbitrary
universe `u`. Over any algebraically closed field `k : Type u`, let `G` be a
smooth connected affine group scheme and let `i : U ⟶ G` be a closed subgroup
with `U` smooth, connected and unipotent. If the range of `i` lies in every
Borel subgroup, there is an actual closed subgroup `n : N ⟶ G` with `N`
smooth, connected and unipotent, with normal range containing the range of
`i`. Normality and containment hold on every test scheme.

The Lean proof applies the published construction
`UnipotentAllBorelsEnvelope.unipotentAllBorelsEnvelope_of_statements` to three
published proofs:

- `ImageGeneration.pointedImageGeneration`, from
  `Langlands.GroupScheme.ImageGenerationPointed`, proves
  `PointedImageGenerationStatement.{u}`.
- `solvableUnipotentPart`, from
  `Langlands.GroupScheme.Absolute.SolvableUnipotentPart`, proves
  `SolvableUnipotentPartStatement.{u}`.
- `unipotentClosedSubgroup`, from
  `Langlands.GroupScheme.UnipotentClosedSubgroupProof`, proves
  `UnipotentClosedSubgroupStatement.{u}`.

All three inputs are supplied by theorems at the same universe `u`; no
structural proposition remains a hypothesis of this theorem. The published
target and its imported definitions are unchanged.

The construction generates a closed subgroup from the conjugation morphism
`(g, u) ↦ g i(u) g⁻¹`. Its source is affine and geometrically integral, and
`(1, 1)` maps to the identity, so pointed-image generation gives a smooth
geometrically connected generated subgroup. Equivariance makes its range
normal; the points `(1, u)` give containment of `U`. Fix a Borel `B₀` and its
unipotent part `Bu`. The all-Borel hypothesis puts each rational conjugate of
`U` in `Bu`. Reduced-source factorization promotes this rational containment
to a factorization of the conjugation morphism through `Bu`. Minimality then
makes the generated subgroup a closed subgroup of `Bu`, and the
closed-subgroup theorem proves its unipotence. Geometric connectedness over
the field gives connectedness. Rational points enter only in the
factorization argument; the resulting range conditions quantify over all
test schemes.

This module is an internal, derived application of Library theorems. The
construction and its source comparison are documented in
[`UnipotentAllBorelsEnvelope.md`](UnipotentAllBorelsEnvelope.md); the imported
proof pairs explain the three structural results. The proof introduces
exactly the published hypotheses on `G` and `U`.

Construction: Worker 1393. Assembly and documentation: Worker 1461.
