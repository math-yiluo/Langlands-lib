# The unit Haar comparison and unit integrals of characters

This helper module is internal infrastructure for the proof of
`Langlands.GodementJacquet.LocalTateConductorStatement`. It compares the
target's multiplicative measure `localMultiplicativeHaar F` on `O^×` with
additive Haar measure. It then computes the unit integrals and Gauss integrals
of a character of exact conductor `a`.

## Haar comparison

`unitShell F` is `{x ∈ F | v(x) = 1} = O \ ϖO` (`unitShell_eq`). It is the image
of the integral units in `F` (`range_integralUnits_val`). Adding an element of
`ϖ^n O` with `n ≥ 1` preserves it (`add_mem_unitShell_iff`). Its additive measure
is finite and positive, and equals `ν(O) - ν(ϖO)`.

`setIntegral_integralUnits` is the main comparison. For every additive Haar
measure `ν` and every `g : F → ℂ`,

`∫_{O^×} g(u) d^×u = ν(unitShell)⁻¹ · ∫_{unitShell} g dν`.

No integrability hypothesis is needed. The implemented proof works on the
compact group `K = O^×`, a subtype of `Fˣ`.

- The pullback `λ_K` of `localMultiplicativeHaar F` along `K → Fˣ` is a Haar
  measure (`Measure.IsHaarMeasure.comap` along an open embedding). The
  published `localMultiplicativeHaar_integerUnits` shows that it has total
  mass one.
- The pullback `ν_K` of `ν` along the measurable embedding `e : K → F` is
  finite. It is left invariant: the generic lemma
  `isMulLeftInvariant_comap_of_preimage` reduces this to invariance of `ν`
  under multiplication by `e k`. That invariance follows from the published
  `HarmonicAnalysis.generalScalarHaarScalingStatement`, since the normalized
  absolute value of an integral unit is one.
- Mathlib's `Measure.isMulInvariant_eq_smul_of_compactSpace` gives
  `ν_K = c • λ_K`. Evaluating both sides on `K` gives `c = ν(unitShell)`.
- Both integrals are transported to `K` with `MeasurableEmbedding.integral_map`
  and `map_comap`, and `integral_smul_nnreal_measure` extracts the scalar.

`measure_unitLevel` applies the comparison to the indicator of `1 + ϖ^m O`,
for `m ≥ 1`. That set lies in the shell and is a translate of `ϖ^m O`, so
`μ^×(1 + ϖ^m O) = ν(ϖ^m O) / ν(unitShell)`.

## Character integrals

Let `η : Fˣ →* ℂˣ` have exact conductor `a` (`IsUnitConductor η a` from
`LocalTateUnits`). `extendUnits` extends a function on `Fˣ` by zero to `F`.

- `setIntegral_unitLevel_char`: the integral of `η` over `unitLevel m` is
  `μ^×(unitLevel m)` if `a ≤ m` and `0` otherwise. The vanishing case
  multiplies by some `w ∈ unitLevel m` with `η(w) ≠ 1`.
- `setIntegral_integralUnits_char`: `∫_{O^×} η = 1` if `a = 0` and `0`
  otherwise.
- `extendUnits_add_of_mem_ball`: if `η` is trivial on `1 + ϖ^n O` with
  `n ≥ 1`, then the extension of `η` is invariant on the shell under
  translation by `ϖ^n O`. This holds because `(x + t)/x ∈ 1 + ϖ^n O`.

The Gauss integral is
`gaussIntegral ψ η k = ∫_{O^×} ψ(ϖ^k u) η(u) d^×u`. For `ψ` with integer
conductor:

- `gaussIntegral_of_nonneg`: for `k ≥ 0` the factor `ψ(ϖ^k u)` is one, so
  `G(k) = [a = 0]`.
- `gaussIntegral_eq_zero_of_neg`: `G(k) = 0` for `-a < k < 0`. Take
  `w ∈ 1 + ϖ^{-k} O` with `η(w) ≠ 1`. Then `ψ(ϖ^k w u) = ψ(ϖ^k u)` and the
  multiplicative vanishing principle applies.
- `gaussIntegral_eq_zero_of_lt`: `G(k) = 0` for `k < -max(a, 1)`. Pass to the
  shell integral by the Haar comparison. Then translate by some
  `t ∈ ϖ^{max(a,1)} O` with `ψ(ϖ^k t) ≠ 1`, which leaves the extended
  character unchanged, and apply the additive vanishing principle.
- `gaussIntegral_neg_one`: for unramified `η`,
  `G(-1) = -ν(ϖO) / ν(unitShell)`. Split the shell integral as
  `∫_O - ∫_{ϖO}` and use additive orthogonality from `LocalTateFourier`.

## Provenance

These are the standard local computations behind Tate's local functional
equation and the Gauss-sum description of the epsilon factor; see Tate's thesis
(source `tate-1967-thesis`) and the 1979 survey cited in
`LocalTateConductorStatement.md`. Here they are internal derived lemmas with no
new original-source assertion.
