# Normalized first-block quotient integration

Module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationProof`.
Theorem `Langlands.RankinSelberg.twoBlockFirstBlockQuotientIntegration` has complete type exactly the published closed proposition `Langlands.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationStatement.{uF}`. Worker 27 assembled the proof and authored the measure, kernel, properness, unfolding and normalized tower helpers. Worker 117 authored the determinant-shift and analytic helpers. Worker 235 supplied the positive-lifting and compact-finiteness proof organization reused in the tower and the analytic organization reused by Worker 117.

The theorem covers every canonical p-adic field in universe `uF` and every positive two-block shape. It uses the published actual groups `G = GL_(a+b)`, `H = diag(N_a,N_b)`, `L = diag(GL_a^0,N_b)`, their actual left quotients, determinant slices and `fiberPoint`. It proves all clauses of the existing proposition, including Haar and regularity assertions, compatible quotient existence, sigma-finiteness for every compatible triple, and for every integer `k` an s-finite measurable kernel with the everywhere representative formula and the normalized identity

```text
κk ∘ₘ (νL.restrict mixedSlice0) = νH.restrict blockSlicek.
```

There is no scalar or density. The outer slice is zero for every `k`, and the small inner slice is `k`. The target statement and the Lean/Markdown pairs in its import closure are unchanged.

## Fixed measures and quotient existence

The proof instantiates only the canonical topology, valuation, local-field, countability and Borel structures specified in the statement. Its `μH` is exactly `TwoBlockUnipotentQuotient.blockHaar`, the transport of the product of the two specified unipotent Haar measures. The existing block-measure instances prove its Haar property, regularity and right invariance.

The existential norm-one measure is `normOneHaar F (m 0)`. It is the pullback of the specified first-block ambient Haar through the open subgroup inclusion. The theorem `map_normOneHaar` supplies exactly

```text
map Subtype.val μA0 = μGA.restrict GL_a^0.
```

The induced `μL` is definitionally `mixedHaar F h`, the transport of `μA0 × μNb`. Its established instances prove Haar, regularity and right invariance. The specified first-block unipotent Haar is also right invariant. The three compatible quotient measures exist by `fullUnipotent_compatibleMeasureExists`, `block_compatibleMeasureExists` and `mixed_compatibleMeasureExists`. Thus the subsequent universal assertions about compatible triples have explicit existence witnesses.

For an arbitrary compatible triple `νA`, `νH`, `νL`, compatibility supplies regularity. The quotient spaces are locally compact and second countable, using the canonical general linear group instances and the open quotient maps. The resulting measure instances give sigma-finiteness of all three quotient measures. In particular `νA` is s-finite and finite on compact sets.

## Measurable kernel and s-finiteness

For each integer `k`, the proof obtains precisely the target's `hInvariant` from `normOneRightInvariant_of_isCompatible` and chooses `fiberKernel F h νA hInvariant k`. The construction descends the pushforward of the restricted small quotient measure under `fiberPoint`. Joint continuity makes the representative family measurable. Under left multiplication of an ambient representative by `diag(u,n)` in `L`, the published fiber law replaces the small argument by its right translate by `u`. The norm-one right invariance of `νA` and the zero determinant order of `u` preserve the restricted small measure. This is the published right-translation descent.

`fiberKernel_mk` gives the required measure equality at every ambient representative. `fiberKernel_isSFinite` supplies kernel s-finiteness. Its properness argument lifts compact target sets to compact ambient sets. Fixing one point in a nonempty small-slice preimage makes the ratio of any other point with it norm-one; a compact set in the closed mixed subgroup then covers that preimage through the first quotient coordinate. The closed preimage is compact. Finiteness of `νA` on compacts therefore gives finiteness of every fiber on compact target sets. A common countable compact cover of the locally compact, Hausdorff, second-countable block quotient proves s-finiteness of the kernel.

## Exact normalized composition and determinant transport

The proof uses `(normalized_tower ...).2` to obtain, for every integer `j`,

```text
κ0 ∘ₘ (νL.restrict mixedSlicej) = νH.restrict blockSlicej.
```

That helper first derives the small orbital-kernel identity from compact-test compatibility. Restricting it to the small zero slice identifies its composition with the exact pushforward of `normOneHaar`. Unfolding the specified block product then identifies the integral of a block average over this small zero slice with the mixed average, without a coefficient. Compatibility with the common ambient Haar gives equality on all such compact nonnegative tests. Positive lifting realizes all nonnegative continuous compact quotient tests as block averages. Compact bump functions prove compact finiteness of the composite before regular measure extensionality identifies it with `νH`. Finally the determinant formula for `fiberPoint` restricts the full identity to matching base and target slices.

`fiberKernel_comp_zeroSlice_eq` turns these matching-slice identities into the exact formula required here. It chooses `z : GL_a` with `ord(det z) = k`, using surjectivity of the normalized field order and of determinant in positive rank. Right translation by `z` takes small slice zero exactly to small slice `k` and preserves `νA`. Left multiplication by `diag(z,1)` defines the homeomorphism `mixedLeftShift` of the mixed quotient. Conjugation by `z` preserves the first-block ambient Haar and its restriction to `GL_a^0`; consequently conjugation by `diag(z,1)` preserves `mixedHaar`. The ambient Haar modulus and mixed-subgroup Haar modulus are both one. The quotient automorphism theorem and right invariance therefore make this mixed left shift measure preserving for `νL`, with exact pushforward of outer slice zero to outer slice `k`.

The point identity `fiberPoint q (diag(z,1)g) = fiberPoint (q · z) g` identifies the `k` kernel with the zero kernel evaluated at the shifted base point. Changing variables in the composite gives

```text
κk ∘ₘ (νL.restrict mixedSlice0)
  = κ0 ∘ₘ (νL.restrict mixedSlicek)
  = νH.restrict blockSlicek.
```

This proves the normalized restricted-measure identity itself. It does not assume any quotient disintegration or convergence premise.

## Tonelli, absolute integrability and the published average

With the representative formula and exact composition now proved, `analytic_of_comp_eq` supplies the remaining two conjuncts of the target. The lower-integral composition formula proves Tonelli for every measurable nonnegative extended-real function. `Measure.integrable_comp_iff` proves the stated equivalence between total absolute integrability and almost-everywhere fiber integrability together with base integrability of the fiber integral of the norm.

For measurable complex `f`, quotient induction, the representative formula and `integral_map` identify the published `firstBlockAverage` everywhere with `q ↦ ∫ z, f z ∂κk q`. If `f` is integrable on the total slice, the general kernel composition theorems prove that this average is integrable on the zero outer slice and that its integral equals the total integral. The conclusion includes convergence assertions and is stronger than an equality of totalized Bochner integrals alone. It asserts the average's integrability, hence almost-everywhere strong measurability, with exactly the strength specified by the target.

## Provenance and scope

The existing target formalizes Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions* (1983), registered source `jpss-1983-rankin-selberg`, Section 4.6, printed page 412, equation (6), with the determinant-slice convention of Section 4.2, printed page 406. The retained PDF SHA-256 is `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`; printed page 412 is one-based PDF page 47. The source passage and absence of a project erratum were checked during the earlier source audit. The explicit measures, kernel, sigma-finiteness and integrability criterion are the derived precision of the published target. This proof follows the implemented internal quotient and kernel route described above; the original source states equation (6) without that proof.

No representation, character or analytic hypotheses are added. This theorem does not address equation (7), half-modulus covariance, Fourier or Mellin identities, factor identities, Section 9.3 disintegration, or the distinct unipotent-radical tower. The proof depends on the existing target and the separately authored first-block helpers; no downstream integration result is assumed.
