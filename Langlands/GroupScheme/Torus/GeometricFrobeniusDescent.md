# Geometric recovery after Frobenius descent

Authors: Worker 1442.

This internal supporting construction composes the two actual recovery
isomorphisms in finite-model Frobenius descent. For fields `k` and `Ω` in an
arbitrary common universe, a finite model `D` of a specified inclusion
`i : T → G_Ω`, and descent data `D₀ : TorusDescent D.inclusion`, the definition
`Model.recoverDescent` returns `TorusDescent i`. Its base torus and closed
inclusion are those of `D₀`. Its recovery isomorphism over `Ω` is the canonical
direct-to-iterated pullback comparison followed by the extension of
`D₀.recovery` and by `D.recovery`.

`Descent.FiniteStage.comparison_naturality` proves naturality of the
finite-stage comparison by checking projections to the original group.
A private equality criterion compares two homomorphisms into an iterated
pullback after projection to the original group: compose with the canonical
direct-pullback comparison, then use the pullback universal property and the
maps' base compatibility. The projection laws of the finite-stage comparison
and of base-changed homomorphisms give naturality. Applying it to
`D₀.inclusion`, substituting the two recovery equations, and cancelling the
ambient comparison proves the exact recovered-inclusion equation.

`Model.geometricDescentOfFrobenius` assumes `k` finite, `Ω/k` algebraic,
`G` affine, and all-test Frobenius invariance of `range i`. It applies
`Model.descentOfFrobenius` and the preceding composition, retaining recovery
over the original extension. The existing maximality lemmas for
`TorusDescent` therefore apply to the specified original inclusion.

`geometricTorusDescentOfFrobenius` additionally assumes local finite
presentation of `G` and starts directly from the specified closed split torus,
without requiring a supplied finite model. It chooses that model using
`TorusFiniteModel.model` and applies the preceding construction.

`IsMaximalTorus.exists_descent_of_frobenius_range_eq` starts with the same
splitness and invariance hypotheses and maximality of `i`. It returns the
actual descended commutative torus, closed inclusion and recovery isomorphism,
maximality over `k`, maximality of its actual pullback to `Ω`, and the exact
recovery equation. The two maximality conclusions follow from the published
`TorusDescent` recovery and reflection lemmas, without forward preservation
of arbitrary maximal tori. No commutativity assumption is imposed on `G`,
and no characteristic or positive-rank restriction is used.

The provenance is internal. The inputs are the actual finite-model data and
finite-field descent from `Torus.FrobeniusDescent`, the finite-model
construction, and the maximality lemmas from `Torus.MaximalDescent`.
The new step is projection-based naturality and composition of recovery
isomorphisms. This module does not construct a Frobenius-invariant geometric
maximal torus or prove the finite-field existence target.
