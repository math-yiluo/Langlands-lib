# Proof of the continuous kernel vectors on a coset space

The theorem `Langlands.QuotientIntegration.quotientConvolutionKernel`
proves the published proposition
`Langlands.QuotientIntegration.QuotientConvolutionKernelStatement.{uG}`
(module `Langlands.Analysis.Local.QuotientConvolutionKernelStatement`)
exactly: the theorem's type is that proposition at universe `uG`, with all
of its hypotheses. The module imports only the target statement and the
published proof `Langlands.Analysis.Local.QuotientL2UnfoldingProof`. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Let `G` be a Hausdorff, locally compact, second countable topological
group with its Borel σ-algebra. Let `H` be a closed subgroup with an
s-finite, right invariant measure `μH` that is finite on compact sets. Let
`μG` be a left invariant measure on `G`, finite on compact sets, and let
`ν` be a measure on `LeftQuotient H`, finite on compact sets, with
`IsCompatible H μG μH ν`. For every `f : C_c(G, ℂ)` there is a continuous
`v : G → L²(ν)` with two further properties. First, for every `x` and every
`φ : L²(ν)`, the function `a ↦ f(a) φ(H (x a))` is integrable and
`⟪v x, φ⟫ = ∫ f(a) φ(H (x a)) dμG(a)`. Second, for every `x` and every
uniform bound `M` of `‖f‖`,
`‖v x‖² ≤ M · (∫ ‖f‖ dμG) · μH.real (H ∩ x S x⁻¹)`, where
`S = supp f · (supp f)⁻¹`. In Lean the last factor is `μH.real` of the
preimage under `Subtype.val` of the conjugate set.

## Auxiliary theorems

The module also proves two auxiliary theorems. Their `omit` clauses drop
instance hypotheses of the section that they do not need.

- `orbitIntegral_norm_le`: let `k : G → ℂ` be bounded by `B` and vanish
  off `K`, and let `D` be a compact set containing every `b c⁻¹` with
  `b, c ∈ K`. Then `∫_H ‖k(η y)‖ dμH ≤ B · μH.real (H ∩ D)` for every `y`.
  If no `η₀ y` lies in `K`, the integrand vanishes. Otherwise every
  contributing `η` satisfies `η η₀⁻¹ ∈ H ∩ D`. The integrand is then bounded
  by `B` times the indicator of the right translate of `H ∩ D`, and
  `measure_preimage_mul_right` gives the measure of that translate. This
  measure is finite because `H ∩ D` is compact: `H` is closed, so the
  inclusion of `H` is a closed embedding.
- `quotientAverageVector_norm_sq_le`: let `k : C_c(G, ℂ)` satisfy the same
  hypotheses with the same `K`, `D` and `B`, and let `w : L²(ν)` be almost
  everywhere equal to the quotient average of `k`. Then
  `‖w‖² ≤ B · μH.real (H ∩ D) · ∫ ‖k‖ dμG`. The proof first writes
  `‖w‖² = ∫ ‖w q‖² dν`, using `L2.inner_def`, `inner_self_eq_norm_sq` and
  `integral_re`. After `Quotient.inductionOn`, the previous theorem gives,
  at each point, `‖avg k‖ ≤ re(avg ‖k‖) ≤ B · μH.real (H ∩ D)`. Hence
  `‖w q‖² ≤ B · μH.real (H ∩ D) · re(avg ‖k‖)(q)` almost everywhere.
  `integral_mono_ae` integrates this bound. The compatibility fields
  `averaging_integrable` and `integral_formula` then evaluate
  `∫ avg ‖k‖ dν = ∫ ‖k‖ dμG`.

## Main proof

1. Vectors and pairing. For each `x`, apply the published
   `quotientL2Unfolding` to the weight `b ↦ star (f (x⁻¹ b))`. By `choose`
   this gives `v x`, almost everywhere equal to the quotient average of the
   weight, together with integrability and
   `⟪v x, φ⟫ = ∫ star (k g) φ(H g) dμG`. `Integrable.comp_mul_left` and
   `integral_mul_left_eq_self` (left invariance of `μG`) make the
   substitution `g = x a`. Since `star (star (f a)) = f a`, this gives
   property 2.
2. Bound. Apply `quotientAverageVector_norm_sq_le` with `K = x · supp f`
   and `D = x S x⁻¹`. The set `D` is compact as a continuous image of the
   compact set `S`. Then `integral_mul_left_eq_self` identifies the `L¹`
   norm of the translated weight with `∫ ‖f‖ dμG`.
3. Continuity at `x₀`, through `Metric.tendsto_nhds`. Fix a compact
   neighbourhood `W` of `x₀`, and set `K = W · supp f`, `D = K K⁻¹` and
   `C = μH.real (H ∩ D) · μG.real K`. Equip `G` with the right uniformity
   `IsTopologicalGroup.rightUniformSpace`. Then
   `HasCompactSupport.uniformContinuous_of_continuous` gives a
   neighbourhood `U` of `1` such that `|f p.1 − f p.2| < ε` whenever
   `p.2 p.1⁻¹ ∈ U`. Take `x ∈ W` with `x₀⁻¹ x ∈ U`. The pair
   `(x⁻¹ b, x₀⁻¹ b)` meets this condition for every `b`, so the difference
   weight `k = hfun x − hfun x₀` is bounded by `ε`. It also vanishes off
   `K`. Its unfolding vector equals `v x − v x₀`, by `ext_inner_right`,
   `inner_sub_left` and `integral_sub`. The auxiliary bound and
   `∫ ‖k‖ ≤ ε · μG.real K` give `‖v x − v x₀‖² ≤ ε² C`. With
   `ε = δ / (√C + 1) / 2`, this is smaller than `δ²`.

## Provenance

This proof is an internal analytic argument, not a transcription of a proof
in the literature. The statement's own Markdown records how the statement
relates to the kernel construction in the proof of Getz–Hahn, *An
Introduction to Automorphic Representations* (2024), Lemma 9.3.3. Getz–Hahn
obtain their kernel from the Riesz representation theorem. This proof
instead constructs `v x` explicitly as an `H`-average through the published
unfolding theorem, and derives the bound and continuity from the orbital
estimate above.

Worker 116 of an earlier project instance wrote the Lean proof and its
explanation in the shared draft of the parent program task
`34b81620-20d7-4059-9b08-6bedd1c1c029`. Worker 968 adopted the unchanged
Lean file for this focused proof task and revised this explanation.
