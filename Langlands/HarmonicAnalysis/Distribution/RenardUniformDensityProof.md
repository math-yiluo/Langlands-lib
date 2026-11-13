# Renard II.3.12: proof of the uniform density range and discrete criteria

Worker 69, Task 5526. The theorem
`Langlands.HarmonicAnalysis.Distribution.RenardUniformDensity.statements` proves the
published proposition
`Langlands.HarmonicAnalysis.Distribution.RenardUniformDensity.Statements` at its full
universe parameter `uG`. It proves all five conjuncts under the target's original
hypotheses: arbitrary Hausdorff, locally compact, totally disconnected groups and any
Borel left Haar measure. The target pair and its imports are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The statement's Markdown gives the locators: the II.3.12 Lemma, the following
Dirac paragraph, Remarks 1–2 and the Proposition (printed pp.51–52 / PDF
pp.57–58), together with II.3.7 Proposition (ii) (printed p.47 / PDF p.53) for
the modular factor.
The route below is an internal deduction from the published Library and pinned
Mathlib. It does not transcribe the source's proof.

The only imports beyond the statement module are published proofs and
definitions:
`RenardConvolutionProof`, `RenardHaarDensityProof`, `RenardModularProof`,
`Hecke.CommonInvarianceProof` and `Hecke.NormalizedIndicator`. No new statement or
axiom is introduced.

## Auxiliary lemmas

- `inversion_mem_compactlySupported`: if `D` vanishes on tests vanishing on a
  compact `Z`, then its inversion vanishes on tests vanishing on `Z⁻¹`.
- `inversion_mem_distributionsRight` / `inversion_mem_distributionsLeft`:
  inversion exchanges left and right `K`-invariance. This uses the published
  intertwining identities `inversionDistributions_leftDistributions` and
  `inversionDistributions_rightDistributions`.
- `exists_test_separating`: distinct points `x ≠ y` are separated by a test
  function. A compact neighbourhood of `x` together with Mathlib's clopen basis
  for locally compact, Hausdorff, totally disconnected spaces gives a compact clopen `V`
  with `x ∈ V` and `y ∉ V`. The characteristic test of `V` (published
  `Hecke.TestFunction.characteristic`) separates them.
- `testDensity_injective`: transfers the published
  `RenardHaar.density_injective` through the inclusion of test functions into
  locally constant functions.
- `testDensity_mem_distributionsLeft`: if `f(kx) = f(x)` for all `k ∈ K`, then
  `f μ` is left `K`-invariant. Mathlib's `integral_mul_left_eq_self` provides
  the change of variables.

## Fifth conjunct: inversion density

`inversion_testDensity` (and hence `inversionDensity`) applies the published
`RenardModular.inversionDensity`. That result gives a locally constant `d` equal to
`x ↦ (renardModular x)⁻¹` with `inversion(μ) = d μ` as distributions on locally
constant functions. The required test function is
`g = multiplyTest d (inversion f)`, so `g(x) = (renardModular x)⁻¹ f(x⁻¹)` pointwise.
To compare the distributions on a test `φ`, evaluate the inversion density identity
at the locally constant function `(inversion f)·φ` and rearrange the product.

## First conjunct: the uniform range

The three uniform spaces are unions over compact open subgroups. The proof
establishes the chain of inclusions

    range(testDensity μ) ⊆ Both ⊆ Left ⊆ range,   Both ⊆ Right ⊆ range,

from which the three set equalities follow by antisymmetry. Injectivity is
`testDensity_injective`.

- **range ⊆ Both** (`testDensity_mem_compactDistributionsBoth`). Given `f`, let
  `g` be the inversion test function from the fifth conjunct. The published
  `Hecke.TestFunction.commonCompactOpenBiInvariance` supplies one compact open
  subgroup `K` under which both `f` and `g` are bi-invariant. Compact support of
  `f μ` comes from `RenardHaar.testDensity_compactlySupported`, and left
  `K`-invariance from `testDensity_mem_distributionsLeft`. For right invariance,
  `g μ` is left `K`-invariant, so its inversion is right `K`-invariant. That
  inversion is `f μ` by the fifth conjunct and the involutivity
  `inversionDistributions_inversionDistributions`.
- **Both ⊆ Left, Both ⊆ Right**: projection from the defining infima.
- **Right ⊆ range** (`mem_range_of_right`). Let `D` be compactly supported
  and right `K`-invariant for a compact open subgroup `K`, and let `T` be `D` as a
  compact distribution. Let `e` be the published normalized indicator
  `μ(K)⁻¹ 1_K` (`Hecke.HeckeAlgebra.normalizedIndicator`). Its integral is `1` by
  `integral_indicator_const` and `compactOpen_complex_mass_ne_zero`. The witness
  is the published `leftTestFunction T e`. The published
  `convolution_testDensity_left` gives `testDensity μ (leftTestFunction T e) = T * e μ`,
  so it remains to show `T * e μ = D`. By the published `convolution_eq_pairing`,
  `(T * e μ)(φ)` is a compact-support pairing of `T` with
  `x ↦ ∫ e(y) φ(xy) dμ(y)`. By `compactSupportPairing_eq_of_agrees` and
  `compactSupportPairing_testDensity`, this pairing equals `D` applied to the
  partial integral of the product test `leftDensityKernel e φ`, which is
  `(x, y) ↦ e(y) φ(xy)`. The published Fubini identity
  `distribution_partialIntegral` turns this into `∫ D(slice_y) dμ(y)`. Here
  `slice_y = e(y) · ρ(y)φ`. For `y ∈ K`, right invariance gives
  `D(ρ(y)φ) = D(φ)`. For `y ∉ K`, `e(y) = 0`. Hence the integrand is `e(y) D(φ)`,
  and the integral is `D(φ)` because `e` has mass one.
- **Left ⊆ range** (`left_subset_range`). If `D` is compact and left
  `K`-invariant, its inversion is compact (`inversion_mem_compactlySupported`)
  and right `K`-invariant. By the previous item it equals `f μ` for some `f`.
  The fifth conjunct gives `g` with `inversion(f μ) = g μ`, and involutivity
  gives `D = g μ`.

`uniformRange` assembles these inclusions.

## Second conjunct: Dirac membership

By the first conjunct, `dirac g` lies in the range exactly when it is in the
uniform left space.

- (`discrete_of_dirac_mem`) Suppose `δ_g` is left invariant under a compact
  open `K`. For `k ∈ K` with `k ≠ 1`, `kg ≠ g`, so `exists_test_separating`
  gives `φ` with `φ(kg) ≠ φ(g)`. However, left invariance evaluated at `φ`
  forces `φ(kg) = φ(g)`. Therefore `K = {1}`, so `{1}` is open and Mathlib's
  `discreteTopology_of_isOpen_singleton_one` makes `G` discrete.
- (`dirac_mem_left_of_discrete`) In a discrete group the trivial subgroup `⊥`
  is open and compact (a singleton). Every Dirac is compactly supported (the
  published `compactDirac`) and trivially `⊥`-invariant.

## Third conjunct: unit criterion

- (unit ⇒ discrete) Let `e` be a two-sided unit of `HeckeAlgebra μ`. For a test
  `φ`, evaluate the identity `e * inversion φ = inversion φ` at `1`. Unfolding the
  published function convolution gives `∫ e(y) φ(y) dμ(y) = φ(1)`, that is,
  `testDensity μ e = dirac 1`. Then the second conjunct gives discreteness.
- (discrete ⇒ unit) The second conjunct gives `e` with `e μ = δ_1`. For each `h`,
  the published `RenardConvolution.heckeCompatibility` identifies the density of
  `e * h` (resp. `h * e`) with the compact-distribution convolution of the
  densities. The published unit laws `convolution_dirac_one_left` /
  `convolution_dirac_one_right` reduce this to `h μ`, and `testDensity_injective`
  gives `e * h = h` and `h * e = h`.

## Fourth conjunct: two-sided ideal

Given `D = f μ`, the witness is `F = compactTestDensity μ f`, which coerces to
`D` by definition.

- `T * F` is `testDensity μ (leftTestFunction T f)` by
  `convolution_testDensity_left`.
- For `F * T`, `testDensity_mem_compactDistributionsBoth` gives a compact open
  `K` with `F` left `K`-invariant. The published `convolution_dirac_left` turns
  this into `δ_k * F = F` for `k ∈ K`. Associativity
  (`convolution_associative`) then shows that `δ_k * (F * T) = (δ_k * F) * T = F * T`.
  So `F * T` is a compact, uniformly left-invariant distribution. By the first
  conjunct it lies in the range.

## Assembly

`statements` is the conjunction
`⟨uniformRange, diracMembership, unitCriterion, ideal, inversionDensity⟩`.
