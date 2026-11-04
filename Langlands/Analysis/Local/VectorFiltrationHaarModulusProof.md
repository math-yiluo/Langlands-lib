# Proof of Haar moduli along a filtration with vector-space quotients

Author: Worker 1423.

This module proves
`Langlands.HaarModulus.VectorFiltrationHaarModulusStatement` as
`Langlands.HaarModulus.VectorFiltration.vectorFiltrationHaarModulus`. It uses the helper
module `Langlands.Analysis.Local.NormalSubgroupHaarModulus` (Haar moduli across a closed
normal subgroup), the Library's `Langlands.Haar.compactOpenCoverUnimodularity`, the
Library's determinant change of variables `Langlands.HarmonicAnalysis.haarMeasure_map_matrix`,
the Library's `secondCountableTopology` and `t2Space` for nonarchimedean local fields,
and `Langlands.Geometric.haarChar_eq_of_conjugacy` from
`Langlands.HarmonicAnalysis.HaarConjugacy` for invariance under continuous group conjugacy.

## Auxiliary declarations

All are in namespace `Langlands.HaarModulus.VectorFiltration`.

- `smul_measure_cancel`, `haar_smul_cancel`: `a • ρ = b • ρ` forces `a = b` when some set
  has positive finite `ρ`-measure, in particular for a Haar measure on a locally compact
  group (a compact neighbourhood of the identity).
- `subgroupOfContinuousMulEquiv h`: for `A ≤ B`, Mathlib's `Subgroup.subgroupOfEquivOfLe`
  as a topological group isomorphism `A.subgroupOf B ≃ₜ* A`.
- `scalingWithZero : k →*₀ ℝ≥0`: `distribHaarChar k` extended by `0` at `0`;
  `scalingWithZero_of_ne_zero` evaluates it at a nonzero element.
- `map_mul_left_eq_scalingWithZero`: for a regular additive Haar measure `ν` on `k` and
  `a ≠ 0`, `ν.map (a * ·) = (scalingWithZero a)⁻¹ • ν`. It follows from Mathlib's
  `distribHaarChar_mul`, since the preimage of `s` under `x ↦ a x` is `a⁻¹ • s`.
- `quotient_mulEquivHaarChar_eq`: let `K` be a normal subgroup of `H` and `q : H → k^n`
  a continuous, open, surjective homomorphism to the additive group with kernel `K`.
  Suppose it intertwines an automorphism `α` with a linear automorphism `L`. Then the
  automorphism of `H ⧸ K` induced by `α` (`quotientGroupAutomorphism`) has Haar modulus
  `distribHaarChar k (det L)`.
  Proof: `q` descends to a bijective, continuous, open map, hence a homeomorphism
  `e : H ⧸ K ≃ₜ k^n` satisfying `e (z w) = e z + e w` and `e ∘ αQ = L ∘ e`. The image `ρ`
  of a Haar measure `μQ` of `H ⧸ K` is an additive Haar measure on `k^n`. By
  `haarMeasure_map_matrix` (with `χ = scalingWithZero` and the matrix of `L`),
  `ρ.map L = (|det L|)⁻¹ • ρ`. Pulling back by `e` gives `μQ.map αQ = (|det L|)⁻¹ • μQ`,
  and `mulEquivHaarChar_smul_map` with `haar_smul_cancel` gives the modulus.
- `step_mulEquivHaarChar`: let `H` be locally compact and Hausdorff, with every element
  in a compact open subgroup. In the setting above, with `K` locally compact,
  `mulEquivHaarChar α = mulEquivHaarChar (α|K) * distribHaarChar k (det L)`.
  Proof: `K` is closed, as the preimage of `0`, and normal, as the kernel of a
  homomorphism. `compactOpenCoverUnimodularity` makes the Haar measures of `H` and of
  `K` right invariant. Then
  `QuotientIntegration.mulEquivHaarChar_eq_mul_quotientGroupAutomorphism` and
  `quotient_mulEquivHaarChar_eq` combine.

## Main proof

Substitute `U = F 0`. By induction along the chain, using `_hFle`, every `F r` with
`r ≤ N` lies in `F 0`. Each such `F r` is closed in `G`: `F (r + 1)` is the image under the
closed embedding `F r → G` of the closed set `q r ⁻¹' {0}` (`_hqker`, `_hqc`). Every
element of `F r` lies in a compact open subgroup of `F r`: pull back a compact open
subgroup of `F 0` given by `_hcover` along the inclusion. The preimage is compact
because `F r → G` is a closed embedding.

The claim, proved by induction on `j` with `r + j = N`, is the following. For every `r`
and every proof `h` that `g` normalizes `F r`, the modulus of `x ↦ g x g⁻¹` on `F r` is
`∏_{s ∈ [r, N)} distribHaarChar k (det (L s))`.

- `j = 0`: then `r = N` and `F N = ⊥`. So `F r` is a subsingleton, hence compact, and
  `mulEquivHaarChar_eq_one_of_compactSpace` gives `1`, the empty product.
- `j + 1`: then `r < N`. First, `g` normalizes `F (r + 1)`, by `_hqker` and `_hqL` and
  the injectivity of `L r`; the hypothesis `_hFg` is not used. Apply
  `step_mulEquivHaarChar` to `H = F r`, `K = (F (r + 1)).subgroupOf (F r)`, `α` the
  conjugation and `q r`, `L r`. The restriction `α|K` is identified with conjugation on
  `F (r + 1)` by the existing `Langlands.Geometric.haarChar_eq_of_conjugacy`
  along `subgroupOfContinuousMulEquiv`.
  The induction hypothesis and `Finset.prod_eq_prod_Ico_succ_bot` finish the step.

For `r = 0`, `j = N`, the claim is the conclusion, since `closedNormalizerCharacter` at
`g` is by definition `mulEquivHaarChar` of the normalizer conjugation, and
`Finset.range N = Finset.Ico 0 N`.
