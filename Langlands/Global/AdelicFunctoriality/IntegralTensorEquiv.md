# Actual number-field completed-integer tensor equivalence

This module constructs the canonical algebra equivalence
`Op tensor_(O_K) O_L ≃ product_(q above p) Oq`
for the original rings of integers and actual completed valuation rings.
It is a proved bridge from the existing exact integral-image theorem to the
coefficient-algebra interface used in the Weil point topology comparison.

## Source and inputs

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, Example 4.2, printed p.10, uses integral models in the adelic Weil
comparison. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This algebra equivalence is derived arithmetic for that integral step.

The inputs are number fields `K` and `L` in independent arbitrary universes,
an algebra structure `K -> L`, and any actual
`p : HeightOneSpectrum (NumberField.RingOfIntegers K)`. No extra finite-field
extension or local-degree premise is supplied; the number-field instances
provide finiteness. The index is the full original `FinitePlacesAbove L p`,
not a selected subfamily. `Op` and `Oq` are the existing adic completed
integer subrings, with their original embeddings.

## Original coefficient structures and maps

The declarations lie in
`Langlands.Global.AdelicFunctoriality.IntegralTensor`.
A scoped algebra instance gives `O_K` its action on `Oq` through the original
`O_K -> O_L -> Oq`. The corresponding scalar tower is literal. A second
scalar-tower proof identifies this action with the one through `Op` and the
original `FiniteExtension.completionIntegersMap`. It follows from the proved
original-field formula for `FiniteExtension.completionMap`.

`tensorMap p` is the original `Op`-algebra homomorphism from
`Op tensor_(O_K) O_L` into the product of every original `Oq`. Its
`tensorMap_tmul` law identifies the underlying field value with
`completionMap p q a * algebraMap O_L Lq b`. The equality uses the actual
scalar tower through the completed integer subring, without substituting a
different upper-field embedding.

`comparison_comm` compares this map to the published
`integralTensorComparison L p` and `integralTensorInclusion L p`. After the
original tensor-order interchange, the published comparison of the original
integral inclusion equals the underlying field tuple of `tensorMap`.
The proof is tensor induction, using the existing pure-tensor formula and
commutativity in the original completed fields.

## Bijectivity and the algebra equivalence

`inclusion_injective` proves injectivity of the published
`integralTensorInclusion`. The actual `O_L` is torsion free over the Dedekind
ring `O_K`, hence flat by Mathlib's existing instance. Tensoring the original
inclusion `Op -> Kp` with this flat module preserves injectivity. This helper
has no `NumberField L` hypothesis; it retains the original lower-number-field
and field algebra structures used to obtain the flatness instance.

`tensorMap_injective` now uses the injective tensor-order interchange, this
flat integral inclusion, and the bijective published field comparison from
`integralLocalTensorComparison`. The proved square transfers equality of
original integer tuples through those injections.

`tensorMap_surjective` uses the exact integral-image equality already proved
in `IntegralLocalComparisonProof`. Each tuple of actual `Oq` elements gives
an underlying completed-field tuple in the full integer lattice. The
published equality produces an original integral tensor mapping to it.
Interchanging tensor factors and applying the proved square gives an actual
preimage under `tensorMap`. Equality is checked in each original valuation
subring by subtype equality. No new approximation or compactness proof is
assumed or repeated.

`tensorEquiv p` is `AlgEquiv.ofBijective` of this same canonical map.
`tensorEquiv_tmul` retains its original completed-field component formula.
`tensorEquiv_one_tmul` gives the actual algebra map from `O_L` to `Oq`, as
required by the Weil coefficient comparison.

## Reuse and scope

The substantial integral approximation and closed-image proof is imported
unchanged through the published `integralLocalTensorComparison`. The present
module adds the original coefficient-order algebra map, its comparison
square and the flat injectivity bridge. It constructs the actual integer
ring algebra equivalence; it does not yet assert the integral Weil point
topology, compatibility with global models or the adelic homeomorphism.
