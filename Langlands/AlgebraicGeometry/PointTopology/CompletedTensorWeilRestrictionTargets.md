# Actual upper-place targets of the completed-tensor Weil decomposition

Author: Worker 208.

This is a derived construction for the completed-tensor and finite-product
identities in Brian Conrad, *Weil and Grothendieck approaches to adelic
points*, December 31, 2011, Example 4.2, printed page 10. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
That original page was read. No source-specific errata file was found in the
current Library or project notes.

Conrad decomposes the algebra obtained by extending a global field to a
completion into the product of the completed upper fields. The corresponding
base-changed scheme is the disjoint union of its upper-place base changes.
To use this inside the actual Weil construction, the target obtained by
successive tensor base change, coefficient transport, and factor pullback
must be identified with the original scheme over the upper field. This
module constructs that identification using actual spectrum maps and
canonical pullback pasting. The arbitrary-ring helper is a derived
generalization of this step; the arithmetic specializations here cover
number fields, with the function-field obligation retained below.

All types and schemes lie in one arbitrary common universe. In the general
construction, `A`, `B`, and `C` are commutative rings with `A`-algebra
structures on `B` and `C`. Each ring `D i` has given `B`- and `C`-algebra
structures. The index type is arbitrary and need not be finite or nonempty.
The input is an actual algebra equivalence

```text
e : C ⊗[A] B ≃ₐ[C] (∀ i, D i)
```

satisfying the explicit compatibility law
`e (1 ⊗ b) i = algebraMap B (D i) b`. This is the structural compatibility
needed to recover the original `B`-scheme, rather than just some scheme over
the same factor rings. No finite generation, projectivity, topology,
separatedness, finite type or quasi-projectivity is required for the target
identification.

`tensorCoefficientSpecFactor_comp` derives from that law that the actual
composite

```text
Spec(D i) → Spec(∀ j, D j) → Spec(C ⊗[A] B) → Spec(B)
```

is `Spec.algebraMap B (D i)`. The three arrows are respectively the spectrum
of the coordinate projection, the spectrum of `e`, and the spectrum of the
right tensor inclusion. The proof combines the contravariant spectrum maps
and applies extensionality on `B`; the required equation is exactly the
supplied `1 ⊗ b` law.

For any actual scheme `Y` over `Spec B`,
`tensorCoefficientFactorTarget` is the actual iterated target

```text
factor_i (coefficientPullback_e (ringBaseChange B (C ⊗[A] B) Y)).
```

Each operation is an actual categorical pullback. The construction
`tensorCoefficientFactorTargetIso` identifies this object with
`ringBaseChange B (D i) Y` over `Spec(D i)`. Its implementation composes two
canonical `pullbackLeftPullbackSndIso` maps with `pullback.congrHom` for the
proved composite spectrum equality. Its `_hom_fst` theorem states that the
map followed by the projection to `Y` is precisely the composite of the
three original pullback projections. Thus the map preserves the actual
projection to `Y` and is fixed canonically; no factor-target isomorphism is
assumed as input.

For number fields `K` and `L` with their given `Algebra K L`,
`finitePlaceTensorEquiv K L v` is the actual algebra equivalence

```text
K_v ⊗[K] L ≃ₐ[K_v] (∀ q : FinitePlacesAbove L v, L_q).
```

It is `AlgEquiv.ofBijective` applied to the existing `finiteTensorMap v`
and the published proof `(completedTensorComparison K L).1 v`.
The `_apply` theorem identifies its function with that map, and
`finitePlaceTensorEquiv_one_tmul` retains its exact right-factor law.
Here the index subtype consists of **all** actual height-one primes of the
integer ring of `L` lying above `v`, with the existing lies-over instances.
The scalar actions on completions are those constructed from the continuous
completion embeddings in `AdelicFunctoriality.Extension`. No tensor
bijectivity or local-degree theorem remains an extra hypothesis.

`finitePlaceWeilRestrictionFactorTargetIso` specializes the canonical
pullback identification with these actual fields, this equivalence and the
proved right-factor law. Its endpoint is the actual base change
`ringBaseChange L (q.1.adicCompletion L) Y`.

`infinitePlaceWeilRestrictionFactorTargetIso` gives the same identification
for **all** `q : InfinitePlacesAbove L v`, including real and complex
completions, using the existing `infiniteTensorEquiv v` and
`infiniteTensorMap_one_tmul v`. Its endpoint is
`ringBaseChange L q.1.Completion Y`. Both specializations retain the general
exact projection identity by unfolding their definitions. They impose no
additional geometry on `Y`.

The completed tensor bijectivity proofs are reused from the published
Library by Lean name. In particular, `CompletedTensorComparisonProof`
provides the finite arithmetic theorem and `Norm` provides the infinite
one; the present construction adds no arithmetic assumption or axiom and
does not reprove those results.

This unit supplies actual number-field coefficient decompositions and
factor-target identifications. It does not yet compose the tensor,
coefficient, product and complete-field point homeomorphisms. Function-field
completed-tensor realizations, integral models, geometric preservation of
Weil restriction, and the global adelic comparison remain obligations of
the parent all-five-sections task. No whole-paper completion is asserted.
