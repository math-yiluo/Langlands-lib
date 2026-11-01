# The normalized two-block quotient tower

Module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientTower`,
namespace `Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegration`.

Author: Worker 235.

This helper module supports the proof of
`Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement`
(JPSS 1983, Section 4.6, printed pages 411-412). Write `G = GL_(t+1)(F)`,
`N` for the upper unipotent subgroup, `H = blockUnipotent h F` for the
block-diagonal unipotent subgroup, `R = M((m 0 + 1) × (m 1 + 1), F)` for the
radical, `π : H \ G → N \ G` for the published `projection` and
`x ↦ [u(x) g]_H` for the published `fiberPoint`. Fix a kernel `κ` from
`N \ G` to `H \ G` with the radical fiber law

`κ [g]_N = map (fun x => fiberPoint h F x g) μR` for every `g`,

where `μR` is an additive Haar measure on `R`, and write
`c = μR {x | ∀ a b, x a b ∈ O}` for the mass of the integral rectangle. The
module proves that `κ ∘ₘ ν_N = c • ν_H` for compatible quotient measures, that
this identity restricts along `π`, and that compatible quotient measures are
σ-finite. It then packages these with the analytic module into
`TowerTailStatement`. That proposition is the final conjunct of the target
statement (everything after the choice of `κ`) under explicit hypotheses on
`μH`, `μN`, `c` and `κ`. The module does not construct `κ`, does not prove
that the fixed measures are Haar or right invariant, and does not prove that
`c` is positive and finite. Those are separate parts of the proof.

## Provenance

JPSS (source ID `jpss-1983-rankin-selberg`), Section 4.6, printed pages
411-412, integrate a function on `H \ G` by integrating first along the fibres
`x ↦ [u(x) g]_H` of `π` and then over `N \ G`, using `N = H ⋉ R` and the
matching factorization of Haar measures. The source uses this without stating
it as a lemma. The kernel formulation, the normalization by `c` and all
statements below are internal content of this proof. The objects come from the
published modules `TwoBlockUnipotentQuotientData` (quotients, `fiberPoint`,
`projection`, `radicalAverage`), `Measures` (`generalLinearHaar`,
`unipotentHaar`) and `QuotientMeasure` (`IsCompatible`). The module uses the
helper modules `TwoBlockUnipotentQuotientCoordinates` (Haar transport
`map_coordinates_prod`, unit mass `blockMeasure_integral`) and
`TwoBlockUnipotentQuotientAnalysis` (`analytic_of_comp_eq_smul`).

## Instances

The module declares private instances: local compactness and second
countability of the matrix spaces, of `N` and of `H`; second countability of
`GL_n(F)`; the
Hausdorff property, local compactness and second countability of `H \ G`; and
local compactness and second countability of `N \ G`. Quotient maps by
subgroups are open, so second countability descends to the quotients.

## Generic local field (section `Tower`)

In this section `F` is a nonarchimedean local field with a Hausdorff,
second-countable topology. All the measurable structures involved are
arbitrary Borel structures.

- `continuous_fiberPoint_left`: `x ↦ [u(x) g]_H` is continuous on `R`.
- `continuous_projection'`: `π` is continuous.
- `lintegral_fiberPoint_quotientAverageReal` (fiber unfolding): let `μH` be a
  left and right invariant Haar measure on `H` with mass one on the integral
  points of `H`, let `unipotentHaar F t` be right invariant, and let `μR` be
  additive Haar. Let `f` be a continuous, compactly supported, nonnegative
  real function on `G`. Then for every `g`,
  `∫⁻ x, ofReal (Av_H f [u(x) g]_H) ∂μR = c * ofReal (Av_N f [g]_N)`. Here
  `Av_H` and `Av_N` are the published `quotientAverageReal` for `μH` and
  `unipotentHaar F t`. The proof writes `Av_H f [u(x) g]_H` as a lintegral
  over `H` and applies Tonelli on `H × R`. It then pushes `μH.prod μR`
  forward along the coordinates `(b, x) ↦ b u(x)`, which gives
  `c • unipotentHaar F t` by `map_coordinates_prod`.
- `lintegral_comp_quotientAverageReal` (tower unfolding): under the same
  hypotheses on `μH` and `μR`, for any kernel `κ` with the radical fiber law,
  any measure `ν_N` on `N \ G` and any nonnegative
  `f : C_c(G, ℝ)`, `∫⁻ z, ofReal (Av_H f z) ∂(κ ∘ₘ ν_N) =
  c * ∫⁻ q, ofReal (Av_N f q) ∂ν_N`. This is `Measure.lintegral_bind`. The
  fiber law and `lintegral_map` reduce the inner integral to the fiber
  unfolding.
- `comp_eq_smul` (normalized tower identity): let `μG` be a measure on `G`
  that is finite on compacts, let `μH`, `μR` be as above with `c ≠ ⊤`, and
  let `unipotentHaar F t` be right invariant. Let
  `κ` have the radical fiber law. If `ν_N` is compatible with
  `(μG, unipotentHaar F t)` and `ν_H` is compatible with `(μG, μH)`, then
  `κ ∘ₘ ν_N = c • ν_H`. The proof has three steps.
  1. By the tower unfolding and the quotient integral formula
     (`RecursiveIntegration.lintegral_quotientAverageReal`), both measures
     integrate `ofReal ∘ Av_H f` to `c * ∫⁻ ofReal ∘ f ∂μG` for every
     nonnegative `f : C_c(G, ℝ)`.
  2. Every nonnegative `φ : C_c(H \ G, ℝ)` is `Av_H f` for some nonnegative
     `f : C_c(G, ℝ)` (`realQuotientPositiveLifting`). Bounding the indicator
     of a compact set by such a `φ` shows that `κ ∘ₘ ν_N` is finite on
     compacts. It is therefore regular on the second-countable, locally
     compact Hausdorff space `H \ G`. The measure `c • ν_H` is regular
     because `ν_H` is regular and `c ≠ ⊤`.
  3. The two regular measures agree on every `ℝ≥0`-valued compactly supported
     continuous function, so they are equal
     (`Measure.ext_of_integral_eq_on_compactlySupported_nnreal`).
- `comp_restrict_eq_smul` (restriction): for any measure `μR`, any kernel `κ`
  with the radical fiber law, any measures `ν_N`, `ν_H`, any `c` with
  `κ ∘ₘ ν_N = c • ν_H` and any measurable `s ⊆ N \ G`,
  `κ ∘ₘ ν_N|_s = c • ν_H|_(π⁻¹ s)`. Since `π [u(x) g]_H = [g]_N`
  (`projection_fiberPoint`), `κ q (A ∩ π⁻¹ s)` equals `κ q A` for `q ∈ s` and
  `0` otherwise. Both sides of the claim then evaluate on a measurable `A` to
  `(κ ∘ₘ ν_N)(A ∩ π⁻¹ s)`.

## The tail of the statement over a `p`-adic field

- `TowerTailStatement` (a `Prop`-valued `abbrev`): fix a `p`-adic field `F`
  with the topology, valuation, local-field and Borel data of the target
  statement, and the same `t`, `m`, `h` and measurable structures (Borel on
  `F`, `G`, `N`, `H`, the block factors and both quotients). Let
  `μG = generalLinearHaar F t`, `μN = unipotentHaar F t`, and let `μH` be the
  target's fixed block measure, the pushforward of
  `Measure.pi (fun i => unipotentHaar F (m i))` along `blockUnipotentEquiv`.
  The statement says the following. Assume `μH` is a Haar measure and `μN`
  and `μH` are right invariant. Let `μR` be an additive Haar measure on `R`
  with `c ≠ 0` and `c ≠ ⊤`, and let `κ` be an s-finite kernel with the
  radical fiber law. Let `ν_N` and `ν_H` be compatible with `(μG, μN)` and
  `(μG, μH)`. Then `ν_N` and `ν_H` are σ-finite. Moreover, for every
  measurable `s`, with `ν_Ns = ν_N|_s` and `ν_Hs = ν_H|_(π⁻¹ s)`:
  1. `κ ∘ₘ ν_Ns = c • ν_Hs`;
  2. `∫⁻ q, ∫⁻ z, f z ∂κ q ∂ν_Ns = c * ∫⁻ z, f z ∂ν_Hs` for measurable
     `f : H \ G → ℝ≥0∞`;
  3. for measurable `f : H \ G → ℂ`, `f` is `ν_Hs`-integrable if and only if
     `f` is `κ q`-integrable for `ν_Ns`-almost every `q` and
     `q ↦ ∫ z, ‖f z‖ ∂κ q` is `ν_Ns`-integrable;
  4. if such an `f` is `ν_Hs`-integrable, then `radicalAverage F h μR f` is
     `ν_Ns`-integrable and
     `∫ q, radicalAverage F h μR f q ∂ν_Ns = c.toReal • ∫ z, f z ∂ν_Hs`.

  From the two compatibility hypotheses on, the Lean text copies the end of
  the last conjunct of `TwoBlockUnipotentQuotientIntegrationStatement`, so
  the target's proof can apply `tail_of_fiberLaw` to its chosen kernel.
- `tail_of_fiberLaw : TowerTailStatement`. The proof re-installs the
  statement's instances and takes the unit mass of `μH` on the integral
  points from `blockMeasure_integral`. The measure `generalLinearHaar F t` is
  Haar, hence finite on compacts. So `comp_eq_smul` gives
  `κ ∘ₘ ν_N = c • ν_H`. Compatible measures are regular, hence finite on
  compacts, and both quotients are σ-compact, so `ν_N` and `ν_H` are
  σ-finite. For each measurable `s`, `comp_restrict_eq_smul` gives item 1.
  `analytic_of_comp_eq_smul`, applied to the s-finite measure `ν_N|_s`, gives
  items 2 to 4.
