# Integral local tensor comparison

The theorem
`Langlands.Global.AdelicFunctoriality.integralLocalTensorComparison`
proves exactly the published proposition
`Langlands.Global.AdelicFunctoriality.IntegralLocalTensorComparison`.
Import `Langlands.Global.AdelicFunctoriality.IntegralLocalComparisonProof`.

The fields `K : Type u` and `L : Type v` lie in independent universes. The
hypotheses are `[Field K] [Field L] [NumberField K] [NumberField L]
[Algebra K L]`, with arbitrary `p : HeightOneSpectrum (𝓞 K)`. There is no
additional premise. Write `A = 𝓞 K`, `B = 𝓞 L`,
`K_p = p.adicCompletion K`, and `O_p = p.adicCompletionIntegers K`.
For `q : FinitePlacesAbove L p`, write `L_q = q.1.adicCompletion L` and
`O_q = q.1.adicCompletionIntegers L`. The three conclusions are:

1. The actual canonical map `T = integralTensorComparison L p`, from
   `B ⊗[A] K_p` to `Π q, L_q`, is bijective.
2. For `i = integralTensorInclusion L p`, the range of `T ∘ i`, with domain
   `B ⊗[A] O_p`, is exactly `Set.pi Set.univ (fun q => (O_q : Set L_q))`.
3. `T` is a `Set.BijOn` from `Set.range i` to that same product.

Every auxiliary lemma is private. The proof imports the published target and
maps without editing them. In particular, the source set in the third clause
is the actual inclusion range; this proof does not assert injectivity of `i`.

## Implemented proof

The private `comparison_bijective` composes the bijectivity of the published
`integralTensorTransportBijective K L p` with the finite-place component of
`completedTensorComparison K L`. The existing identity
`finiteTensorMap_integralTensorTransport` identifies their composite with
`T`. Neither the localization transport nor the completed-field comparison
is reproved.

For the integral image, `integral_image_subset` uses tensor induction and the
published pure-tensor formula

```
T (i (b ⊗ x)) q =
  algebraMap B L_q b * (FiniteExtension.completionIntegersMap p q.1 x : L_q).
```

Both factors belong to `O_q`; closure under multiplication and addition gives
the required containment.

The opposite containment uses closedness and approximation. First,
`tensor_coefficients` expresses every element of `B ⊗[A] O_p` as
`∑ j, b j ⊗ x j`, where `b : Fin n → B` is any finite generating family
for the `A`-module `B` and `x : Fin n → O_p`. For a pure tensor, finite
generation writes its first factor as an `A`-linear combination of the
`b j`; the balancing relation transfers those coefficients to `O_p`.
Tensor addition adds the coefficient vectors.

The number-field instances provide `Module.Finite A B`, so
`Module.Finite.exists_fin` supplies such generators. In
`integral_image_closed`, the map

```
(Fin n → O_p) → Π q, L_q,
x ↦ (fun q => ∑ j, algebraMap B L_q (b j) *
  FiniteExtension.completionMap p q.1 (x j))
```

is continuous: each coordinate is a finite sum of constant multiples of a
continuous completion map composed with subtype inclusion and coordinate
evaluation. Its range equals the integral image by `tensor_coefficients`
and the pure-tensor formula. The published
`Langlands.Global.isCompact_adicCompletionIntegers K p` makes `O_p`
compact; hence its finite power is compact. The product of the Hausdorff
completed fields is Hausdorff, so the image is closed. The temporary
`CompactSpace O_p` instance is local to this proof.

Next, `integer_approximation` strengthens the published
`Langlands.Global.exists_integer_sub_valued_le` to a strict bound by any
nonzero value in `ℤᵐ⁰`. Choose a global uniformizer for `q` and a power
whose valuation is below the requested bound, then use that power as the
nonzero integer in the published lemma. The identity
`Langlands.Global.valued_algebraMap_integer` evaluates its completed
valuation.

`simultaneous_integer_approximation` applies this at each place in a finite
set and uses Mathlib's
`IsDedekindDomain.exists_forall_sub_mem_ideal` to combine the chosen global
integers. The distinct underlying height-one primes are comaximal. The
congruence error lies in a sufficiently high power of the corresponding
prime, so `intValuation_le_pow_iff_mem` bounds it strictly. The
nonarchimedean triangle inequality combines the congruence and approximation
errors.

`integral_product_subset_closure` consequently places every integral tuple
in the closure of the diagonal image of `B` in `Π q, L_q`. A neighborhood of
zero in the product imposes conditions at finitely many coordinates.
`Valued.is_topological_valuation` supplies a valuation ball within each
coordinate neighborhood. Surjectivity of the restricted valuation onto its
value group selects a representative for each ball's nonzero threshold.
The simultaneous approximation lemma meets all those conditions.

Finally, the diagonal image of `b : B` belongs to the integral image, witnessed
by `b ⊗ 1`. Closedness therefore puts its closure in the integral image.
Combining the two containments proves `integral_image_eq`. The final theorem
assembles this equality and bijectivity, then proves `BijOn` by restricting
the global injectivity of `T` and using the range equality for surjectivity.

## Scalar actions and indexing

All tensor products use the existing `A`-actions. The `A`-action on `B`
comes from the field extension, and its action on `O_p` is the canonical
integral completion action. The proof opens the published `FiniteExtension`
scope. Thus `completionMap p q.1` and `completionIntegersMap p q.1` use
the existing completion algebra and scalar towers. No new completion
algebra, action, or tower is installed. The finite-generator argument uses
only the tensor balancing relation over `A`.

Every tuple and approximation is indexed directly by the Library's
`FinitePlacesAbove L p`. The Chinese remainder argument proves distinctness
of underlying primes by `Subtype.ext` and `HeightOneSpectrum.ext`. It
requires no reindexing through Imperial's `Extension` type; the published
`finitePlacesAboveEquiv` is therefore unnecessary in this implementation.

## Provenance and adaptations

Worker 461 adapted ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`. The registered original is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `ImperialCollegeLondon--FLT/source`.

The relevant upstream locations are
`FLT/DedekindDomain/Completion/BaseChange.lean:364–547`, especially the
closed integral image and closure comparison at lines 428–547, and the
final `integerBaseChangeLinearEquiv_bijOn` at lines 854–870.
The finite simultaneous approximation and product closure arguments adapt
`FLT/DedekindDomain/AdicValuation.lean:331–403`.

The main changes are specialization to number fields in independent
universes, direct use of the Library's canonical maps and finite places,
reuse of its published transport and completed-field comparison, and
replacement of the upstream open-lattice argument by the compact
finite-coefficient image argument above. The approximation uses the
Library's already published local integer approximation instead of
porting Imperial's local residue machinery. The value-group conversion in
the product closure proof uses `ValueGroup₀.restrict₀_surjective` and
`Valuation.restrict_lt_iff` directly. The audit's compatibility patches
for external module names, completion-map evaluation and biscalar
instances are not needed by this implementation.

The original `BaseChange.lean` notice is
“Copyright (c) 2025 Kevin Buzzard. All rights reserved.” Its authors are
Kevin Buzzard, Andrew Yang, and Matthew Jasper. The separate original
`AdicValuation.lean` notice is
“Copyright (c) 2025 Matthew Jasper. All rights reserved.” Its author is
Matthew Jasper. Both copyright notices, the original author names, the
Apache-2.0 header, and a modification notice identifying both adapted files
are retained in the Lean file. The upstream license is at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source and dependency assessment is recorded in the published
[finite-adele base-change audit](../../../notes/reuse/finite-adele-base-change-audit.md).
The imported approximation and compactness results are documented in
[AdeleQuotientCompactProof.md](../AdeleQuotientCompactProof.md) and
[IntegralFiniteAdeles.md](../IntegralFiniteAdeles.md).
This proof was written by Worker 461 without using an unpublished worker
draft. Worker 52 supplied the focused task specification.

## Development validation

In the prepared Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment, the complete module
passes a Lake build with no errors or warnings. Declaration inspection
reports a theorem with universe parameters `u` and `v` and only
`propext`, `Classical.choice`, and `Quot.sound` as axioms. Independent
semantic review, exact-target validation and publication are separate from
these development checks.
