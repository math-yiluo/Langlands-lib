# The actual integral tensor decomposition at a function-field place

This module constructs an algebra equivalence from the completed-integer
base change of the **actual integral closure** of an original lower valuation
ring to the product of the actual integer rings at **all** upper completions.
Both injectivity and surjectivity are proved on these original rings.

## Source and hypotheses

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, Example 4.2, printed p.10, uses integral models to obtain the adelic Weil
comparison. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This completed-integer decomposition is derived arithmetic for that integral
reduction. It does not by itself assert an integral scheme or adelic point
homeomorphism.

Let `k`, `K` and `L` be fields in one arbitrary universe, with their three
algebra structures, and fix `p : AlgebraicCurve.Place k K`. Write `R` for the
original `p.toValuationSubring`, `S` for the actual
`curvePlaceIntegralClosure L p`, `Kp` for `curvePlaceCompletion p`, and `Op` for
its original `curvePlaceCompletionIntegers p`. The upper index is the entire
`CurvePlacesAbove k L p`, and `Oq` denotes the actual upper completed integer
ring. The final equivalence is `Op ⊗[R] S ≃ₐ[Op] (∀ q, Oq)`.

The final construction assumes finite `k`, `FiniteDimensional K L`,
`IsScalarTower k K L`, an original `Algebra (RatFunc k) K` presentation with
`IsScalarTower k (RatFunc k) K`, and `FunctionField k K`. No separability of
`L/K` or of this original rational-function presentation is imposed. The
actual integral-closure module finiteness, all-place field tensor equivalence
and integral approximation are proved imports, not assumptions. No
`FunctionField k L` presentation is required.

## Original maps and field transport

All public names below lie in `Langlands.Global.CurvePlaceIntegralTensor`.
`originalIntegersMap p q` is the original inclusion `S -> q.toValuationSubring`
followed by its original completed-integer embedding. It is an `R`-algebra
homomorphism. Its `_coe` law identifies the underlying field value with the
original completion image of `(b : L)`.

Scoped algebra instances supply the original `R` action on `Oq` through
`Op`, the original `S` action on `Oq`, and their compatible scalar towers.
The algebra instances have priority 50. `integralTensorMap p` is the canonical
`Op`-algebra homomorphism from `Op ⊗[R] S` to every original `Oq`, assembled
from these two maps. Its `_tmul` law says that the underlying upper completed
field value is `completionMap p q a * algebraMap L Lq (b : L)`.
`integralTensorFieldMap` is the same map viewed in the product of completed
fields, with the same literal pure-tensor law. These constructions and laws
need only the original fields and algebra structures.

Under `FiniteDimensional K L`, `fieldTensorTransport p` gives
`Kp ⊗[R] S ≃ₗ[Kp] Kp ⊗[K] L`. The actual integral closure localizes to the
original `L` at the nonzero lower denominators. Mathlib's localized-module
base-change equivalence gives `K ⊗[R] S ≃ₗ[K] L`; cancellation of base change
then yields the displayed transport. Its `_tmul` law sends `a tensor b` to
`a tensor (b : L)`. This route uses no separability or finite constants.

`integralTensorInclusion` tensors the actual injection `Op -> Kp` with `S`.
`integralTensorInclusion_injective` proves its injectivity: the integral
closure is torsion free over the original DVR, hence flat, and flat tensoring
preserves the original injection. Its pure-tensor law is literal.
`fieldComparison` composes `fieldTensorTransport` with the proved original
all-upper-place field tensor equivalence. The original ring maps agree in
`fieldComparison_inclusion`, proved by tensor induction. Thus
`integralTensorMap_injective` follows by the two injective field comparisons.

## Compact image, integral approximation and surjectivity

`integralTensorFieldMap_range_isClosed` proves that the integral tensor image
in the full product of upper completed fields is closed. The actual `S` is a
finite `R` module, so choose finitely many original generators `b_i`. Tensor
bilinearity expresses every tensor as `sum a_i tensor b_i` with `a_i` in `Op`.
The corresponding field-valued map from the finite coefficient space
`Fin n -> Op` is continuous, by the original completion-map continuity and
finite sums and products. The actual `Op` is compact by the proved finite
residue-field and completeness construction in
`FunctionFieldAdelesLocallyCompactProof`. Its finite coefficient space is
therefore compact. The upper field product is Hausdorff, so this continuous
image, which equals the actual integral tensor range, is closed. This
closed-image lemma does not use the constant-field tower.

`integralTensorFieldMap_range` identifies that range with the full product
integer lattice. One containment follows directly from the actual `Oq`
values of `integralTensorMap`. Conversely the range contains every original
`S` image, as tensors `1 tensor b`. The original integral closure is dense
in the entire product integer lattice by
`CurvePlaceIntegralLattice.productIntegers_subset_closure`. Closedness of the
integral tensor range therefore gives the other containment.

`integralTensorMap_surjective` lifts each actual tuple of upper completed
integers using that exact range equality, then uses subtype equality in each
original completion. `integralTensorEquiv p` is the algebra equivalence of this
same actual map, with its proved injectivity and surjectivity. Its `_tmul` law
retains the original component formula. Its `_one_tmul` law identifies each
component with the actual algebra map `S -> Oq`, ready for the integral Weil
comparison.

## Provenance and retained obligations

The finite-coefficient and compact-image arguments adapt the published
`AdelicFunctoriality.IntegralLocalComparisonProof` (Worker 461), itself adapted
from Imperial FLT commit `923d45174c500aa1d994ba973bac38ea39eacbf7` under
Apache-2.0. The Lean header retains that attribution and the upstream license
location. The present construction uses actual curve places and the local
integral closure, retains inseparability, proves integral injectivity by
flatness, shortens the coefficient transport by cancellation of base change,
and uses the proved full lattice density in place of a new Chinese-remainder
approximation proof.

This unit is an algebraic comparison on actual integer rings. The associated
finite-module topology, integral Weil point homeomorphism, compatibility with
spreading to global models and the adelic homeomorphism remain separate
obligations of the parent task.
