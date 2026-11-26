# Convolution on a compact part of the positive rational quotient

This module proves that an integrated compact convolution on the
positive rational quotient, followed by restriction to a compact set, is a
compact operator. It also builds the two auxiliary objects used for this:
multiplication by a set indicator on `L²`, and the continuous family of
`L²` kernel rows of a compact convolution.

## Indicator multiplication

For any measure space `(X, ν)` and measurable `D ⊆ X`,
`quotientL2Indicator hD : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν` sends a class `x` to the
class of `D.indicator x`. Additivity and homogeneity hold almost
everywhere, and the operator has norm at most `1`, because
`‖(D.indicator x) q‖ ≤ ‖x q‖` pointwise. `quotientL2Indicator_ae` states
that the representative of the image agrees with `D.indicator x` almost
everywhere.

## Setting

Let `F` be a number field and `G` an affine group scheme over `F`, locally
of finite type. Fix the positive-central data `T`, `i`, `hi`, `I`, `e` and `hc`.
Write `A = AdelicGroupPoints F G`, `Γ = positiveRationalSubgroup F G T i`,
`Q = PositiveRationalQuotient F G T i` and
`μQ = positiveRationalQuotientHaarMeasure F G T i`. Let
`R f hf = haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f hf`
be the integrated right action of a weight `f` for the left Haar measure of `A`.

## Declarations

- `continuous_positiveQuotient_rightTranslate`: the map
  `(q, a) ↦ LeftCosetSpace.rightTranslate Γ a q` from `Q × A` to `Q` is
  continuous. The product of the open quotient map
  `LeftCosetSpace.mk Γ` with the identity is a quotient map, and on
  representatives the map is multiplication in `A` followed by the
  quotient map.

- `exists_positiveQuotientL2ConvolutionRows`: for `f : C_c(A, ℂ)` there is
  a continuous `k : Q → Lp ℂ 2 μQ` with the following properties. For every
  `x : A` and every `φ`, the function `a ↦ f a * φ [x a]` is Haar
  integrable and `⟪k [x], φ⟫ = ∫ f a * φ [x a] da`. For every `φ`,
  `R f hf φ` agrees almost everywhere with `q ↦ ⟪k q, φ⟫`.

  Proof. The Library theorem
  `Langlands.QuotientIntegration.quotientConvolutionKernel` applies to the
  closed subgroup `Γ` (`isClosed_positiveRationalSubgroup`), its measure
  `positiveRationalSubgroupHaarMeasure` and the compatibility
  `positiveRationalQuotientHaarMeasure_isCompatible`. It gives a continuous
  row map `v : A → Lp ℂ 2 μQ` with the stated integral formula. The inner
  products of `v (γ x)` and `v x` with every `φ` are equal, by
  `LeftCosetSpace.mk_subgroup_mul`, so `v` is left `Γ`-invariant. It
  therefore descends along `LeftCosetSpace.lift` to a continuous `k` on
  `Q`. `Langlands.Analysis.integratedTranslationPointwise`, applied to the
  bounded right action `haarQuotientL2BoundedRightAction` and the
  measurable action map above, shows that `R f hf φ` agrees almost
  everywhere with the pointwise integral `q ↦ ∫ f a * φ (q · a) da`. At
  `q = [x]` this integral is `⟪k [x], φ⟫`.

- `isCompactOperator_positiveQuotientL2CompactPart`: for compact measurable
  `D ⊆ Q`, the operator `quotientL2Indicator hm ∘L R f hf` is compact.

  Proof. The rows `k` are continuous, so their norms are bounded by some
  `C` on `D`. Set `kD q = ⟪k q, ·⟫` for `q ∈ D` and `kD q = 0` otherwise.
  The truncated operator is represented almost everywhere by
  `φ ↦ (q ↦ kD q φ)`, and `‖kD q‖² ≤ max C 0 ^ 2 · 1_D(q)`. This bound is
  integrable because `μQ D` is finite, as `μQ` is locally finite
  (`positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure`).
  `Langlands.Analysis.OperatorIdeals.hilbertSchmidtDominatedEvaluation`
  gives Hilbert–Schmidt summability, and
  `Langlands.Analysis.OperatorIdeals.hilbertSchmidtCompact` gives
  compactness.

## Provenance

In Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
the proof of Lemma 9.3.3 (printed pp. 247–248) represents evaluation by
an `L²` kernel with uniformly bounded rows. Such an operator is
Hilbert–Schmidt. This module applies the same criterion, in the dominated
form, to a convolution truncated to a compact set, where the continuous
rows are bounded. No estimate at the cusp is needed here.
