# Coordinates for actual affine base change

Author: Worker 208.

This derived infrastructure concerns the actual affine base changes used by
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed page 6, immediately before Theorem 3.6 and in (3.6.1).
The evaluation topology is the affine topology described in Proposition 2.1,
printed page 2. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For a compatible commutative algebra tower `C → D → A` and a commutative
`C`-algebra `B`, `AlgPoint.baseChangeEquiv` is the actual tensor universal
property

`Hom_C(B, A) ≃ Hom_D(D ⊗[C] B, A)`.

The forward map sends `d ⊗ b` to `algebraMap D A d * p b`; its inverse
evaluates at `1 ⊗ b`. These formulas are stated explicitly. With the existing
evaluation topologies and an actual topological ring structure on `A`,
`AlgPoint.baseChangeHomeomorph` constructs a homeomorphism with precisely this
underlying equivalence. Forward continuity tests each tensor coordinate and
uses tensor induction: a pure tensor gives multiplication of a fixed value
by a continuous evaluation, and a sum uses continuous addition. Inverse
continuity follows directly from evaluation at `1 ⊗ b`.

No topology on `C`, `D` or `B` is assumed; in particular no continuity of a
structure map from either base ring is assumed. There is no finite-generation,
local-ring, separation or Hausdorff assumption. The rings `C`, `D` and `B`
are in an arbitrary common universe `u`; the value ring `A` may lie in an
independent universe `v`. The topological-ring assumption is imposed on the
forward continuity theorem and homeomorphism, while the inverse continuity
theorem requires only a topology.

For an arbitrary actual affine scheme `X` over `Spec C`,
`ringBaseChange_isAffine` supplies affineness of its actual pullback.
`ringBaseChangeSpectrumIso` identifies the actual base change of `Spec B`
with `Spec (D ⊗[C] B)` as a scheme over `Spec D`. It first interchanges the
two pullback factors and then uses Mathlib's actual tensor-spectrum
isomorphism. The equation over `Spec D` is its first-projection formula.
Finally, `ringBaseChangeAffineOverIso` applies the pullback functor to the
canonical global-section presentation of `X` and composes with that
tensor-spectrum isomorphism. Thus its coordinates are the actual global
sections of `X`, with the base structure induced by the original structural
morphism.

These are derived constructions, rather than separately numbered assertions
of Conrad's paper. They supply algebra-point topology and actual-scheme
coordinate infrastructure. The identification of their point comparison
with `ringPointBaseChangeEquiv`, and the topology theorem for that map, are
separate obligations. This module does not construct local completions,
valuation rings, adele rings or nonaffine point-space topologies.
