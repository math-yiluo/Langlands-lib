# A test-independent Mellin convergence threshold: proof

Worker 235 authored this proof and its explanation. The target statement pair
was authored by Worker 468 and is imported unchanged.

`Langlands.RankinSelberg.uniformFiniteFunctionMellinConvergence.{uF}` proves
exactly `Langlands.RankinSelberg.UniformFiniteFunctionMellinConvergenceStatement.{uF}`
at an arbitrary field universe `uF`, with no further hypothesis. It applies the
helper theorem `UniformMellin.uniformFiniteFunctionMellinConvergence_of_pointwise`
to the published theorem `Langlands.RankinSelberg.finiteFunctionMellin`
(module `Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof`).
That published theorem discharges the helper's only premise,
`FiniteFunctionMellinStatement.{uF}`. Only the first, pointwise convergence
clause of that premise is used. Its rational-continuation and
common-denominator clauses are not used.

The target is an internal quantifier strengthening, so the argument below is
derived internal content, not a named literature theorem. The finite-function
conventions are those of the target statement and of the published
finite-function Mellin pair, which cite Jacquet–Piatetski-Shapiro–Shalika
(1979, printed pp. 180–182; 1983, printed pp. 391–392).

## What is retained

The proof introduces exactly the instances that the target installs: the
supplied topology, valuation and local-field structure, and the Borel
structures on the field and its units. Every prime, field, topological
realization, dimension `r` (including `r = 0`), positive weight vector and
finite family `X` (including the empty family) is arbitrary. The measure is the
actual product `Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)`. The
test is an arbitrary Schwartz–Bruhat function on the full additive space
`Fin r → F.Carrier`. The proof adds only proposition-valued instances derived
from the supplied data: Hausdorffness (`T.fieldT2`), total disconnectedness
(`MellinAssembly.field_totallyDisconnected`), σ-finiteness of the supplied
multiplicative Haar measure (`MellinAssembly.localHaar_sigmaFinite`), and second
countability of the field (`T.secondCountableTopology`) and, through
`Units.isEmbedding_val₀`, of its unit group. No different measure or topology
is chosen.

## Implemented argument

Write `ι(a) = (↑(a i))ᵢ` and
`w(s, a) = ∏ᵢ (T.normalizedAbs ↑(a i) : ℂ)^((m i : ℂ) * s)`.

**Translation spans (generic, any monoid `G`).** `translationSpan η` is the
complex span of the left translates `a ↦ η (b * a)`. This is literally the
submodule in the target's finite-function predicate. A translate of a member of
the span is again a member (`translate_mem_translationSpan`), so the span of a
member lies in the span of `η` (`translationSpan_le`). For continuous `η` every
member is continuous (`continuous_of_mem_translationSpan`). Hence every member
of the span of a finite function is a finite function
(`finite_of_mem_translationSpan`). For a basis `e` of the span indexed by
`Fin d` and any `b`, `exists_translate_expansion` writes
`η (b * a) = ∑ₖ C k * e k a` with constants `C` depending on `b`.

**Integrability from a translate (generic).**
`integrable_of_translate_expansion` takes a left-invariant measure on a group
with measurable multiplication. Suppose a function `f` satisfies
`f (b * a) = ∑ₖ C k * (Ψ a * h k a)`, where each `h k` is integrable and `Ψ` is
a.e. strongly measurable with `‖Ψ a‖ ≤ M`. Then `f` is integrable. The finite
sum is integrable by `Integrable.bdd_mul`. Left invariance
(`Integrable.comp_mul_left` with `b⁻¹`) then transfers integrability from
`a ↦ f (b * a)` back to `f`.

**The fixed box test.** `HarmonicAnalysis.exists_compact_clopen` (published in
`RowTensorDecompositionProof`) gives a compact clopen set `B ∋ 0` in
`Fin r → F.Carrier`. `clopenIndicator B` is its indicator, a Schwartz–Bruhat
function `Φ₀` equal to `1` on `B`.

**Dilation.** `exists_dilation` shows that for compact `K` and a neighbourhood
`B` of `0` there is `t ≠ 0` with `t • x ∈ B` for all `x ∈ K`. Joint continuity
of scalar multiplication and the tube lemma
(`IsCompact.eventually_forall_of_forall_eventually`) give a neighbourhood of
`0 ∈ F.Carrier` of admissible scalars. The published
`T.exists_normalizedAbs_ball_subset` (`SchwartzBruhatValuationBoundsProof`)
turns it into a normalized-absolute-value ball of radius `ε`. Since
`q⁻¹ < 1` for the residue cardinality `q > 1`, some `q^(-N) < ε`.
`T.ord_surjective_nonzero` gives `t ≠ 0` of order `N`, so
`T.normalizedAbs t = q^(-N) < ε`.

**Multiplicative weight.** `weight_mul` proves
`w(s, b * a) = w(s, b) * w(s, a)` from `T.normalizedAbs_mul`, nonnegativity of
the normalized absolute value and `Complex.mul_cpow_ofReal_nonneg`.

**Main helper.** Inside `uniformFiniteFunctionMellinConvergence_of_pointwise`,
fix `η ∈ X` and the basis `e = Module.finBasis ℂ (translationSpan η)`.

1. Each `e k` is a finite function. The premise, applied to the singleton
   family `{e k}` with the fixed test `Φ₀`, gives a threshold for
   `a ↦ Φ₀(ι a) * e k a * w(s, a)`. `MellinAssembly.uniform_right` takes the
   maximum `c` over the finite index `Fin d`. This `c` depends only on `η` and
   the fixed box `B`.
2. Let `Φ` be arbitrary and `c < s.re`. Apply `exists_dilation` to the compact
   `tsupport Φ` and `B`, obtaining `t ≠ 0`. Put `b = (fun _ => (t⁻¹ : Fˣ))`
   and `Ψ a = Φ(ι(b * a))`, which is continuous and bounded by `M`
   (`Continuous.bounded_above_of_compact_support`).
3. If `Φ(ι(b * a)) ≠ 0`, then `ι(b * a)` lies in `tsupport Φ`. Hence
   `t • ι(b * a) = ι a ∈ B`, so `Φ₀(ι a) = 1`. Therefore
   `Φ(ι(b * a)) = Φ(ι(b * a)) * Φ₀(ι a)` for every `a`.
4. With the expansion of `η (b * a)` and `weight_mul`, the target integrand
   `f a = Φ(ι a) * η a * w(s, a)` satisfies
   `f (b * a) = ∑ₖ (C k * w(s, b)) * (Ψ a * (Φ₀(ι a) * e k a * w(s, a)))`.
   Every inner function is integrable by step 1. The product measure is left
   invariant (Mathlib's `Measure.pi.isMulLeftInvariant` with σ-finiteness) and
   the unit torus has measurable multiplication. So
   `integrable_of_translate_expansion` proves `f` integrable. The dilation
   changes only the constants `C k * w(s, b)` and `M`, never `c`.

Finally `MellinAssembly.uniform_right` over the finite subtype of `X` gives one
`c` for the whole family. It is chosen before the member, the test and `s`, as
the target requires. For the empty family or `r = 0` the same steps apply
without case distinction.

## Published inputs

- `Langlands.RankinSelberg.finiteFunctionMellin`
  (`FiniteFunctionMellinProof`): pointwise convergence. It discharges the
  premise of `uniformFiniteFunctionMellinConvergence_of_pointwise`.
- `MellinAssembly.uniform_right`, `MellinAssembly.localHaar_sigmaFinite` and
  `MellinAssembly.field_totallyDisconnected` (same module).
- `HarmonicAnalysis.exists_compact_clopen` (`RowTensorDecompositionProof`).
- `PadicField.TopologicalData.exists_normalizedAbs_ball_subset`
  (`SchwartzBruhatValuationBoundsProof`).
- `T.secondCountableTopology` (`PadicScalarHaarScalingProof`) and `T.fieldT2`
  (`LocalField.Topology`).
- `T.normalizedAbs_mul`, `T.normalizedAbs_nonneg`, `T.normalizedAbs_of_ne_zero`,
  `T.ord_surjective_nonzero` and `T.residueCardinality_gt_one`
  (`LocalField.Normalization.Proof`).

These are reused by declaration name. No published file, including the target
pair and its imports, is modified. No two-block, finite-block multiplicativity
or matrix result is used.
