# Renard II.3.13: proof of the criteria for conjugation invariance

Worker 108, Task 5531. Source: Renard, *Représentations des groupes
réductifs p-adiques*, French version of 9 July 2026, II.3.13 Corollary and
proof, (II.3.13.2)–(II.3.13.3), printed pp.55–56 / PDF pp.61–62; source
registration `renard-2026-representations-groupes-reductifs-padiques`.

This proof unit proves the exact published
`Langlands.HarmonicAnalysis.Distribution.RenardCenter.CriteriaStatement`,
at the group universe `uG`, as the theorem
`Langlands.HarmonicAnalysis.Distribution.RenardCenter.criteria`. For every
Hausdorff locally compact totally disconnected group with a left Haar
measure `μ` and every algebraic distribution `T`, conjugation invariance is
equivalent to `TranslationCondition T`, to `TraceCondition μ T` and to
`SandwichTraceCondition T`. All three equivalences are proved by passing
through the translation condition. Only results already in the Library are
used; the helper lemmas below are internal steps of this proof.

## Conventions

`leftTranslate g f x = f (g⁻¹ x)`, `rightTranslate g f x = f (x g)`,
`leftConvolveTest D f x = D (y ↦ f (y⁻¹ x))`,
`rightConvolveTest f D x = D (y ↦ f (x y⁻¹))`, and
`heckeDistribution μ h f = ∫ h y f y dμ(y)`.

## Translation

`pullback_conj_leftTranslate`: pulling `leftTranslate g f` back along
conjugation by `g` gives `rightTranslate g⁻¹ f`. Hence conjugation
invariance at `g` gives the translation identity at `(g, f)`. Conversely,
for `a` and a test `F`, apply the translation identity to
`f = leftTranslate a⁻¹ F`. Then `leftTranslate a f = F`, and
`rightTranslate a⁻¹ f` is the conjugation pullback of `F`
(`isConjugationInvariant_iff_translation`).

## Trace criterion

*Sampling.* `exists_openSubgroup_conj_mem` gives, for a compact set `C` and
an open subgroup `K`, an open subgroup `U` with `y U y⁻¹ ⊆ K` for all `y ∈ C`.
It covers `C` by finitely many cosets `K y` and intersects the corresponding
conjugate preimages of `K`. For tests `f` and `h`, `exists_sampling_level`
takes a common bi-invariance subgroup `K₀` of `f` and `h`. This uses the
published `commonCompactOpenBiInvariance`. It then takes `U` for the compact
support of `h` and returns `K = K₀ ⊓ U`. Thus `h` is right `K`-invariant,
`f` is left `K`-invariant, and `f` is right invariant under `y K y⁻¹` for
every `y` in the support of `h`.

`integral_eq_sampleWeight` applies the published
`Hecke.fixedLevelActionSamples_integral` to the right `K`-invariant function
equal to `φ` on the support of `h` and to `0` elsewhere. It gives
`∫ h φ dμ = Σᵢ dᵢ φ(pᵢ)` for every `φ` that is right `K`-invariant at points
of the support of `h`. The points `pᵢ` and weights `dᵢ` (`sampleWeight`)
depend only on `h` and `K`. The kernels `y ↦ f (x y⁻¹)` and `y ↦ f (y⁻¹ x)`
satisfy this for every `x`. Therefore `f * h` is the actual test
`Σᵢ dᵢ · rightTranslate pᵢ⁻¹ f`, and `h * f` is the test
`Σᵢ dᵢ · leftTranslate pᵢ f`, both with the same weights. The translation
identity gives `T(f * h) = T(h * f)` by linearity (`trace_of_translation`).

*Converse.* Given `g` and `f`, take `K₀` fixing `f` on both sides, and a
compact open `K ≤ K₀ ∩ g⁻¹ K₀ g` (`conjPreimage`). Let `h` be the Hecke
element `μ(K)⁻¹ · leftTranslate g 1_K`, the normalized indicator of `gK`.
By left invariance of `μ` (`integral_leftTranslate_indicator`), integration
against `h` evaluates at `g` any function constant on `gK`. Both kernels are
constant on `gK`. So the witnesses in the trace condition equal
`rightTranslate g⁻¹ f` and `leftTranslate g f`. Their `T`-values agree,
which is the translation identity (`translation_of_trace`).

## Sandwich criterion

`compactSubgroupDistribution_eq_of_const` evaluates the normalized compact
subgroup integral on a test constant on the subgroup. It uses that Mathlib's
`haarMeasure ⊤` has total mass one. Hence `e_K * f = f` for left
`K`-invariant `f` and `f * e_K = f` for right `K`-invariant `f`
(`leftConvolveTest_compactSubgroupHaar`,
`rightConvolveTest_compactSubgroupHaar`). The scalar convolutions with
`dirac g` are `leftTranslate g f` and `rightTranslate g⁻¹ f`.

`leftConvolveTest_sandwich` uses the published mixed associativity
`leftConvolveSmooth_associative` twice and the regularity comparison
`leftConvolveSmooth_eq_test`. These rewrite
`(e * δ_g * e) * f` as `e * (δ_g * (e * f))`. Under the printed local-unit
hypotheses `e * f = f` and `e * (δ_g * f) = δ_g * f`, it equals
`leftTranslate g f`. Symmetrically, `rightConvolveTest_sandwich` uses
`rightConvolveSmooth_associative` with `f * e = f` and
`(f * δ_g) * e = f * δ_g`. It shows `f * (e * δ_g * e) = rightTranslate g⁻¹ f`.
With all four hypotheses, the sandwich identity is the translation identity
(`sandwich_of_translation`). Conversely, take a compact open `K` fixing `f`,
`leftTranslate g f` and `rightTranslate g⁻¹ f` on both sides. Then the four
local-unit hypotheses hold, and the sandwich condition at `(f, g, K)` gives
the translation identity (`translation_of_sandwich`).

## Relation to the source

Renard proves these equivalences while identifying the center. He obtains
(II.3.13.3) from (II.3.13.2) by taking `h = e_K * δ_g * e_K`, and calls the
converse immediate from the formulas for `h * T` and `T * h`. As the
statement unit records, applying the equivalences to an arbitrary algebraic
distribution is an internal extraction of that local-test argument. The
Lean proof instead routes every criterion through the translation identity.
It derives the trace identity by finite sampling of the Hecke element, and
the converse uses the normalized indicator of `gK`.
