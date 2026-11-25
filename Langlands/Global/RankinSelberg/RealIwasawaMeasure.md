# The quotient measure on `N \ GL_n(ℝ)` in logarithmic toral coordinates

Helper module for the convergence part of the real local Rankin–Selberg theory (towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`).
All declarations are proved; there are no hypotheses or axioms
beyond the stated ones.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealIwasawa` and use the Iwasawa coordinates of the
module `RealIwasawa` (`alpha`, `npart`, `kpart`, `torus`, `conjTorus`, `alphaQ`). Here
`G = GL_n(ℝ)`, `N = upperUnipotent n ℝ`, and `N \ G` is the Library's
`QuotientIntegration.LeftQuotient N`.

The main result, `exists_lintegral_alphaQ`, says: for every quotient measure `ν` on
`N \ G` compatible (Library `QuotientIntegration.IsCompatible`) with a left invariant
measure on `G` and a right invariant Haar measure on `N`, there are `κ ≥ 0` and a linear
form `L` on `ℝⁿ` with

`∫⁻ B (alphaQ q) dν(q) = κ ∫⁻ exp (L x) B(x) dx`

for every measurable `B : ℝⁿ → [0, ∞]` (`dx` is Lebesgue measure). No Haar measure of `G`
is computed in coordinates, and no homeomorphism `N \ G ≅ A × K` is used.

## Topology of `N`

- `isClosed_upperUnipotent`: `N` is closed in `G`.
- Instances `instLocallyCompactSpaceRealMatrix`, `instLocallyCompactSpaceRealGL`,
  `instLocallyCompactSpaceUpperUnipotent`: the matrix space, `G` and `N` are locally
  compact. They are ordinary (exported) instances, declared with `instance`, so they take
  part in instance search in every module that imports this one.
- `exists_unipotent_bump`: a continuous, compactly supported, nonnegative `β` on `N` with
  `β 1 = 1` (Urysohn).
- `conjTorusHomeomorph z`: `u ↦ torus z * u * torus (-z)` as a homeomorphism of `N`,
  with `conjTorus_neg_conjTorus`, `conjTorus_zero`, `conjTorus_one`,
  `continuous_conjTorus_right`.

## Lifted functions

For `φ` on `ℝⁿ` and `β` on `N`, the lift is `g ↦ φ (alpha g) * β (npart g)`.

- `continuous_lift`: continuous if `φ` and `β` are.
- `hasCompactSupport_lift`: compactly supported if `φ` and `β` are; its support lies in
  the image of `supp β × supp φ × K` under `(u, y, k) ↦ u * torus y * k`.

## The toral pushforward

For any Borel measurable structure on `N \ G`:

- `measurable_alphaQ`;
- `isFiniteMeasureOnCompacts_map_alphaQ`: if `ν` is finite on compact sets, so is its
  pushforward `ν.map alphaQ` (by `isCompact_alphaQ_preimage`);
- `integral_map_alphaQ`: `∫ φ d(ν.map alphaQ) = ∫ φ (alphaQ q) dν(q)` for continuous `φ`.

## Quasi-invariant measures on `ℝⁿ`

- `exists_integral_ne_zero`: a nonzero measure on `ℝⁿ`, finite on compact sets, has a
  compactly supported continuous `φ` with nonzero integral (Mathlib's
  `Measure.ext_of_integral_eq_on_compactlySupported`).
- `exists_linear_of_quasiInvariant`: let `ρ ≠ 0` be finite on compact sets and suppose
  that for every compactly supported continuous `φ` and every `z`,
  `∫ φ (z + x) dρ(x) = e z * ∫ φ dρ` with `e z > 0`. Then `e = exp ∘ L` for a continuous
  linear `L`. Proof: `e` is multiplicative, and measurable as a quotient of integrals of a
  jointly continuous function; so `log ∘ e` is a measurable additive map `ℝⁿ → ℝ`, hence
  continuous (`AddMonoidHom.continuous_of_measurable`) and `ℝ`-linear.
- `measurable_exp_linear`.
- `withDensity_eq_smul_volume`: under the same hypothesis with `e = exp ∘ L`, the measure
  `exp (L x) dρ(x)` is translation invariant (tested on compactly supported continuous
  functions), so it is `κ` times Lebesgue measure for some `κ ≥ 0` (Mathlib's
  `isAddLeftInvariant_eq_smul`).
- `lintegral_eq_of_withDensity_eq`: if `exp (L x) dρ(x) = κ dx`, then
  `∫⁻ B dρ = κ ∫⁻ exp (-L x) B(x) dx` for measurable `B ≥ 0`.

## The Weil formula for lifts

With Borel measurable structures on `G`, `N` and `N \ G`, a measure `μG` on `G`, a right
invariant `μN` on `N` and a quotient measure `ν`:

- `quotientAverage_lift`: the Library's quotient average of a lift is
  `q ↦ φ (alphaQ q) * ∫ β dμN`, by `alpha_unipotent_mul`, `npart_unipotent_mul` and right
  invariance of `μN`.
- `weil_lift`: if `ν` is compatible, then
  `(∫ φ (alphaQ q) dν) * ∫ β dμN = ∫ φ (alpha g) β (npart g) dμG` for compactly supported
  continuous `φ`, `β` (the `integral_formula` field of `IsCompatible`, applied to the
  complexified lift).
- `weil_translate`: if moreover `μG` is left invariant, then for every `z`,
  `(∫ φ (z + alphaQ q) dν) * ∫ β (conjTorus z h) dμN = (∫ φ (alphaQ q) dν) * ∫ β dμN`.
  Apply `weil_lift` to the translated pair and use left invariance of `μG` under
  `torus z`, together with `alpha_torus_mul` and `npart_torus_mul`.
- `exists_quasiInvariant`: if moreover `μN` is a Haar measure, then
  `ν.map alphaQ` satisfies the hypothesis of `exists_linear_of_quasiInvariant` with
  `e z = (∫ β dμN) / ∫ β (conjTorus z h) dμN` for the bump `β`, both integrals being
  positive (`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`).
- `exists_lintegral_alphaQ`: the main result stated above. `ν.map alphaQ` is nonzero
  (the `nonzero` field), finite on compact sets (the `regular` field and
  `isFiniteMeasureOnCompacts_map_alphaQ`) and quasi-invariant; combine
  `exists_linear_of_quasiInvariant`, `withDensity_eq_smul_volume`,
  `lintegral_eq_of_withDensity_eq` and `lintegral_map`, with the linear form `-L`.

## Provenance

In the proof of Lemma 3.5 (p. 14) of Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), the invariant measure on `N \ GL_n` is written in Iwasawa coordinates `g = a k` as
`dg = J(a) da dk`, where `J(a)` is a character of the diagonal torus whose value Jacquet
leaves symbolic; the estimate then uses the positive-character bound of his Lemma 3.4
(pp. 13–14). This module establishes, in Lean, only the following toral test-function
formula, for compatible quotient measures `ν`: there are `κ ≥ 0` and a linear form `L`
(left unspecified) with `∫⁻ B (alphaQ q) dν(q) = κ ∫⁻ exp (L x) B(x) dx` for every
measurable `B : ℝⁿ → [0, ∞]`. It covers functions of the logarithmic toral Iwasawa
coordinate only; it does not integrate over `K`, does not compute `L`, and does not
identify `exp ∘ L` with Jacquet's `J`. The route (quasi-invariance of the toral pushforward
from the Weil formula, then uniqueness of Haar measure on `ℝⁿ`) is internal.
