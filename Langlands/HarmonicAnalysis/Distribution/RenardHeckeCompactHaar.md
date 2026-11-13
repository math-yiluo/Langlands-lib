# Normalized Haar integration on compact open subgroups (helper for Renard II.3.12)

Worker 70, Task 5527. Source context: David Renard, *Représentations des
groupes réductifs p-adiques*, French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`; II.3.11–II.3.12,
printed pp.51–53 / PDF pp.57–59. The source uses these facts about the
normalized Haar distribution `e_K` of a compact open subgroup `K` without
separate proof. Every declaration in this module is an internal lemma derived
from existing Library carriers and Mathlib; none is a new definition of a source
object. The module lives in namespace
`Langlands.HarmonicAnalysis.Distribution.RenardHecke` and supports the proof
module `RenardHeckeProof`.

Notation: `e_K` is `compactSubgroupHaar K hK`, the Library's normalized
compact-subgroup distribution. It integrates a test over `K` against Mathlib's
`haarMeasure ⊤` on the compact group `K`, with the Borel structure of `K`.

## Compact groups (section `CompactGroup`)

- `isProbabilityMeasure_haarMeasure_top`: on a compact group, `haarMeasure ⊤`
  has total mass one (`haarMeasure_self`).
- `isMulRightInvariant_of_compact`: a left Haar probability measure on a
  compact group is right invariant. The proof applies Mathlib's
  `map_right_mul_eq_modularCharacterFun_smul` and evaluates both sides on the
  whole group. Since the total mass is one, the modular character is `1`.
- `isInvInvariant_of_compact`: such a measure is inversion invariant. By the
  previous lemma, `ν.inv` is again a left Haar probability measure, so
  `isHaarMeasure_eq_of_isProbabilityMeasure` identifies it with `ν`.

## Bridge to an ambient Haar measure (section `Bridge`)

- `integral_probabilityHaar_subtype`: for a compact open subgroup `K`, any
  Borel ambient left Haar measure `μ`, and any Haar probability measure `ν` on
  `K` with the subtype measurable structure,
  `∫ k, f k ∂ν = (μ.real K)⁻¹ * ∫ x in K, f x ∂μ`.
  The comap `μ.comap K.subtype` is a Haar measure on `K`
  (`IsHaarMeasure.comap` along the open embedding). Mathlib's
  `isMulInvariant_eq_smul_of_compactSpace` writes it as `c • ν`, which needs no
  second countability. Evaluating on the whole group gives `c = μ K`, which is
  positive and finite. `integral_subtype_comap` then converts the integral over
  `K` into the set integral.
- `integral_probabilityHaar`: the same formula for any Borel measurable
  structure on `K`. Both Borel structures agree with the subtype one, so the
  proof substitutes it.
- `compactSubgroupHaar_apply_eq`: hence
  `e_K f = (μ.real K)⁻¹ * ∫ x in K, f x ∂μ` for every test `f` and every Borel
  left Haar measure `μ` on `G`.

## Invariance and support (section `Invariance`)

- `compactSubgroupHaar_leftTests`, `compactSubgroupHaar_rightTests`,
  `compactSubgroupHaar_inversionTests`: `e_K` is unchanged by left or right
  translation of the test by an element of `K`, and by inversion of the test.
  These use left invariance of `haarMeasure ⊤` on `K` and the two
  compact-group lemmas above.
- `leftDistributions_compactSubgroupHaar`,
  `rightDistributions_compactSubgroupHaar`,
  `inversionDistributions_compactSubgroupHaar`: the same facts for the
  Library's translated and inverted distributions.
- `support_compactSubgroupHaar_subset`: `support e_K ⊆ K`.
- `compactSubgroupHaar_eq_of_const`: if a test `f` equals the constant `c` on
  `K`, then `e_K f = c`.
- `compactSupportPairing_compactSubgroupHaar_of_const`: the same holds for the
  Library's extended pairing of `e_K` with a locally constant function that is
  constant on `K`. The function is replaced by a test that agrees with it on
  the compact support.
- `convolution_compactSubgroupHaar_left` / `_right`: if a compactly supported
  distribution `D` is invariant under left (respectively right) translation by
  every element of `K`, then `e_K * D = D` (respectively `D * e_K = D`). The
  Library's `convolution_eq_pairing` writes the convolution as an iterated
  extended pairing; `compactPairing_swap` gives the right version. For `k ∈ K`
  the inner function is `D` paired with a translated test, which the invariance
  of `D` makes constant on `K`. The previous lemma then evaluates the outer
  pairing.
- `rightDistributions_convolution` / `leftDistributions_convolution`: right
  (respectively left) invariance of the second (respectively first) factor
  passes to the compact convolution. Translation is convolution with a Dirac
  mass (`convolution_dirac_right`, `convolution_dirac_left`), so the proof
  uses associativity (`convolution_associative`).

## Haar densities (section `Density`)

Here `μ` is a Borel left Haar measure on `G`.

- `testDensity_injective`: `testDensity μ` is injective on tests. This follows
  from the Library's `RenardHaar.density_injective` on locally constant
  functions.
- `heckeDistribution_normalizedIndicator`: the Haar density of the normalized
  indicator `(μ.real K)⁻¹ · 1_K` is `e_K`. This is `compactSubgroupHaar_apply_eq`
  after rewriting the indicator integral. `compactTestDensity_normalizedIndicator`
  is the same equality between compactly supported distributions.
- `convolution_compactTestDensity`: the compact convolution of two test
  densities is the density of their Hecke product `Hecke.TestFunction.convolution μ`.
  It comes from the published `RenardConvolution.heckeCompatibility`.
- `convolution_compactDirac_compactTestDensity`:
  `δ_g * (f μ) = (L_g f) μ`, where `L_g f x = f (g⁻¹ x)`. It comes from the
  published `convolution_testDensity_left`; the resulting kernel is evaluated
  pointwise.
