# Bijectivity of the canonical finite-adele tensor map

The module proves the existing Library statement
`Langlands.Global.AdelicFunctoriality.FiniteAdeleTensorMapBijective` by the theorem
`Langlands.Global.AdelicFunctoriality.finiteAdeleTensorMapBijective_proof`.
Its entire unapplied type is `FiniteAdeleTensorMapBijective.{u, v}`. The two
universe parameters are independent. Unfolding the imported statement gives

```lean
∀ (K : Type u) (L : Type v) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L], Function.Bijective (finiteAdeleTensorMap K L)
```

There are no outer parameters or additional mathematical assumptions. The proof
imports the published statement and canonical map without changing them. All
new helpers are private. This file proves bijectivity; the final algebra
equivalence packaging is a separate construction.

Write `A = 𝓞 K`, `B = 𝓞 L`, `M = A_K = FiniteAdeleRing A K`, and
`A_L = FiniteAdeleRing B L`. Write `K_p` and `O_p` for the completion and its
completed integers. The actual map has source `M ⊗[K] L`, with Mathlib's
standard left-factor `M`-algebra, and target `A_L`, with the published scoped
`FiniteAdeleExtension.instAlgebra` induced by `finiteAdeleInclusion`. Its
pure-tensor value is `finiteAdeleInclusion x * algebraMap L A_L l`.
The proof uses the existing coordinate formula for precisely this map.

## Localization and tensor order

`globalIntegralFieldEquiv K L : K ⊗[A] B ≃ₗ[K] L` comes from
`IsIntegralClosure.isLocalization A K L B`, followed by
`IsLocalizedModule.isBaseChange` and `IsBaseChange.equiv` for the canonical
map `B → L`. Mathlib infers the integral-closure and algebraicity hypotheses
for these number fields. Its value on `1 ⊗ b` is `algebraMap B L b`.

`globalIntegralTransport K L : B ⊗[A] M ≃ₗ[A] M ⊗[K] L` is the composite

```text
B ⊗[A] M
  → B ⊗[A] (K ⊗[A] M)
  → (B ⊗[A] K) ⊗[A] M
  → L ⊗[A] M
  → L ⊗[K] M
  → M ⊗[K] L.
```

The first step is the inverse of `IsLocalization.moduleLid` tensored with
`B`; the second is inverse associativity. The third swaps `B` and `K` and
uses `globalIntegralFieldEquiv`. The fourth is the inverse of
`IsLocalization.moduleTensorEquiv`, and the last is `TensorProduct.comm`.
Every step is `A`-linear, restricting scalars from `K` where necessary.
The actions on `M` are its existing diagonal `K`-algebra and its restricted
`A`-algebra, with Mathlib's scalar tower. The proved pure-tensor formula is

```text
globalIntegralTransport (b ⊗[A] x) = x ⊗[K] algebraMap B L b.
```

This private construction adapts the localization chain in the published
`IntegralTensorTransportProof` from a single completion to `M`. No external
`linearEquivTensorProductModuleLeft` or `leftModuleTensorEquiv` is imported.

## Distributing integral tensors

`integralSubmodule K p : Submodule A K_p` has carrier exactly `O_p`.
Zero and addition are inherited from the valuation subring. Scalar closure
follows from `Algebra.smul_def`, integrality of the image of `a : A`, and
multiplicative closure. The direct carrier construction is necessary because
Mathlib's valuation subring has no `toSubmodule` at this pin.

`adeleModuleEquiv K` identifies `M` with `Πʳ p, [K_p, integralSubmodule K p]`
as `A`-modules. Both underlying functions are identities. The source's
scalar action is diagonal multiplication, while the target's action is
coordinatewise. Its `map_smul'` proof uses `RestrictedProduct.ext` and
`(Algebra.smul_def a (x p)).symm` at each coordinate; it does not assume these
actions are definitionally equal.

`adeleTensorRestrictedEquiv K L` tensors this bridge with the identity on
`B`, then applies the published
`RestrictedProduct.lTensorEquiv A B (adicCompletion K) Filter.cofinite
(integralSubmodule K)`. This is an `A`-linear equivalence from `B ⊗[A] M`
to the restricted product of `B ⊗[A] K_p`, restricted by the submodules
`rangeLTensor A B ... p`. Its coordinate formula is `b ⊗ x ↦ b ⊗ x p`.

The finite-module instance for `B` over `A` is supplied by Mathlib for number
fields. `Module.finitePresentation_of_finite A B` gives finite presentation.
`FaithfulSMul.of_field_isFractionRing A B K L` supplies the faithful action;
Mathlib infers torsion freeness and, over the Dedekind domain `A`, flatness
using `Mathlib.RingTheory.Flat.TorsionFree`. None is a theorem premise.

`tensorRange_eq_integralTensorInclusion` proves by `rfl` that the underlying
set of each restricting submodule is
`Set.range (integralTensorInclusion L p)`. With the explicit carrier and its
inherited subtype action, the tensor of the subtype inclusion and the
published integral tensor inclusion agree definitionally. This equality is
used explicitly in the next restricted-product construction.

## Local comparison, integral subsets and flattening

`globalLocalFiberEquiv K L p` turns the bijective canonical linear map
`integralTensorComparison L p` into an equivalence, using the first clause
of the published `integralLocalTensorComparison K L p`. It then reindexes
its product from `FinitePlacesAbove L p` to
`{q : HeightOneSpectrum B // q.under A = p}` using `finitePlacesAboveEquiv`.
The forward reindexing evaluates at the inverse index equivalence; its
inverse evaluates at the forward one. Underlying primes are unchanged, so
both inverse laws are definitional. These later equivalences are used as
equivalences of types, without an additional target scalar action.

`globalLocalFiberEquiv_bijOn` transports the third clause of
`integralLocalTensorComparison` along that same reindexing. For a tensor
in the integral inclusion range, every output belongs to the corresponding
`O_q`. Conversely, a family of integral values on the restriction fiber is
pulled back to `FinitePlacesAbove`; the accepted local `SurjOn` supplies a
preimage in the actual integral inclusion range. Reindexing it returns the
original family. Injectivity is inherited from the full local equivalence.
Thus the integral subsets, as well as the ambient products, are transported.
The accepted local proof already uses `integralTensorTransportBijective`
and `finiteTensorMap_integralTensorTransport` to identify its comparison
with the completed-field tensor map; those results are imported through
`IntegralLocalComparisonProof`.

`globalLocalRestrictedEquiv` applies the published
`Equiv.restrictedProductCongrRight` to these local equivalences, using the
range equality above and the integral `BijOn` assertion at every place.
Its target is the restricted product of the full products over restriction
fibers, with each restricting subset the product of the `O_q`.

`globalFlattenEquiv` is the published `RestrictedProduct.flattenEquiv'`
for `q ↦ q.under A`. The required convergence from the cofinite filter to
the cofinite filter is the actual theorem `tendsto_under_cofinite` from
`Inclusion`: each restriction fiber is finite. No filter hypothesis is
assumed. Its value at `q` is the value in the `q.under A` fiber at
`⟨q, rfl⟩`. The target restricted product is definitionally `A_L`.

The composite `globalIntegralAdeleEquiv K L` is therefore a bijection
`B ⊗[A] M ≃ A_L`. Its coordinate formula on an arbitrary tensor `z` is

```text
integralTensorComparison L (q.under A)
  (adeleTensorRestrictedEquiv K L z (q.under A)) ⟨q, liesOver_under q⟩.
```

## Equality with the published canonical map

`globalIntegralAdeleEquiv_eq` proves, for every `z : B ⊗[A] M`,

```text
globalIntegralAdeleEquiv z = finiteAdeleTensorMap K L (globalIntegralTransport z).
```

The proof applies finite-adele extensionality and then tensor induction.
For `b ⊗ x`, the left coordinate is
`algebraMap B L_q b * completionMap (q.under A) q (x (q.under A))`.
The right coordinate follows from `globalIntegralTransport_tmul` and the
published `finiteAdeleTensorMap_tmul_apply`. The scalar-tower identity for
`B → L → L_q` and commutativity of multiplication identify the two values.
For a sum, the coordinate formula reduces both sides to the sums of the
corresponding values, using additivity of the tensor distribution, local
comparison, transport and canonical map. Thus the equality holds on the
entire tensor product.

Finally, apply that equality to `globalIntegralTransport.symm z`. The
canonical map on all of `M ⊗[K] L` is the composition of
`globalIntegralAdeleEquiv` with `globalIntegralTransport.symm`. Both are
bijective, which proves the exact imported universal target. This avoids
extending the composite to an `L`-linear equivalence or separately clearing
denominators in a canonical-map comparison.

## Provenance and adaptations

The source is ImperialCollegeLondon/FLT, commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`, retained under registered source
`external-lean-reuse-snapshots-2026-10-21` (source fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`).
The main route is
[`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean:129–252`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean#L129-L252):
localization at 129–141, tensor distribution at 143–160, local comparison
at 162–180, flattening at 182–203, and composition/comparison at 205–252.
The localization antecedent is
[`FLT/DedekindDomain/IntegralClosure.lean:207–297`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/IntegralClosure.lean#L207-L297).
The integral submodule originates at
[`FLT/DedekindDomain/Completion/BaseChange.lean:823–826`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/Completion/BaseChange.lean#L823-L826).

The main and localization source files are copyright 2025 Kevin Buzzard;
the latter and completion file list Kevin Buzzard, Andrew Yang and Matthew
Jasper as authors. The tensor-distribution source is copyright 2025 Matthew
Jasper. The Lean header retains these notices and records modification by
Workers 98 and 100. The upstream Apache-2.0 license is retained at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The Imperial snapshot contains no `NOTICE` file. No Anthropic code is used.

Beyond the audit's compatibility patches (a)–(d), the adaptations are:
number-field specialization and independent universes; replacement of the
external localization helpers by Mathlib's base-change equivalence and
module localization APIs, following the published Worker 50 proof;
`A`-linear tensor distribution through the existing Library equivalence;
a direct submodule carrier and an explicit scalar bridge; the Library's
local canonical comparison and finite-place index; explicit transport of
the integral subsets; type equivalences for reindexing and flattening; and
comparison after a surjective integral transport rather than extension of
scalars and denominator cancellation. The four audited patches concern
external topology, completion and right-action implementations, which this
module does not copy. No additional transparency or heartbeat option is
needed. The internal helpers merely implement this proof route and add no
new general interface.

Worker 100 supplied `integralSubmodule`, `adeleModuleEquiv`,
`adeleTensorRestrictedEquiv` and `tensorRange_eq_integralTensorInclusion`
in shared draft revision 1 for this task. Worker 98 integrated those helpers
and supplied the localization, local reindexing and integral-subset proof,
flattening, canonical-map equality, final theorem and documentation. Both
are contributing coauthors. The published prerequisites are reused by Lean
import and retain their own attribution.

## Development evidence

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, development check
`bed30712-91ce-44a1-914e-df281a2ec545` compiled the complete proof with zero
errors and warnings. Inspection check
`219fbd51-0a18-40b1-8298-af72a8f08935` also completed the Lake build with zero
errors and warnings. It reports a theorem with exactly universe parameters
`u` and `v`, and only `propext`, `Classical.choice` and `Quot.sound` as axioms.
These development checks do not establish independent semantic acceptance
or publication.

Private check `45f26a03-a877-42a4-8f73-62f5bc327289` printed the complete
unapplied type as `FiniteAdeleTensorMapBijective.{u_1, u_2}` and checked direct
assignment at independent universes, with zero errors and warnings.
