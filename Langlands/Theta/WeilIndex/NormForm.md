# The Gauss integral of the norm form

**GKT chapter 3** for the norm form of a quadratic extension, in the language of Gauss integrals
(Definition 3.4, p. 76; Corollary 3.12, p. 80): `γ(ψ_t ∘ N) = η(t) γ(ψ ∘ N)`, which is Corollary
11.4 (p. 315) for the one-dimensional Hermitian space.

The module `Langlands.Theta.WeilIndex.NormForm` computes the regularized integral of
`z ↦ ψ(t N_{E/F}(z))` over a quadratic extension `E` of a nonarchimedean local field `F` of
characteristic `≠ 2` and states the result with the Weil index of `Langlands.Theta.WeilIndex.Defs`:
`γ(ψ ∘ t N) = η(t) γ(ψ ∘ N)`. The Gauss-integral computation is internal (namespace
`Langlands.Theta.Unitary.Internal`); the two theorems with the Weil index are public.

## Content

- `isCharacterOfSecondDegree_mul_norm`: `z ↦ ψ(t N(z))` is a character of second degree on `E`
  (its bicharacter is `ψ(t (N(x + y) - N x - N y))`, and the polar form `t tr_{E/F}(x c(y))` is
  non-degenerate).
- `weilIndex_mul_norm`: **`γ(ψ ∘ t N) = η(t) γ(ψ ∘ N)`** for `t ∈ Fˣ`, `η = normSign E`
  (GKT Corollary 11.4 for `V = ⟨1⟩`, p. 316; Proposition 3.30, p. 88, for the norm form, whose
  determinant is `-d` with `η = (d, ·)_F`). From the internal `hasGauss_norm_mul` and
  `weilIndex_eq_div_norm`: the Weil index is the phase of the Gauss integral
  `g η(t) |t|⁻¹`, `g ≠ 0`.
- `hasGauss_norm_mul` (internal): there is `g ∈ ℂ` with `HasGaussIntegral μ (z ↦ ψ(t N z)) (g · η(t) |t|⁻¹)`
  for every `t ∈ Fˣ`, `η` the quadratic character of `E / F` and `|t| = distribHaarChar F t`. So the
  quadratic character appears in the Gauss integral: this is the source of the condition on `χ` in
  the Leray splitting of `U(ν, ν)` (Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964); Kudla,
  *Splitting metaplectic covers of dual reductive pairs*, Israel J. Math. 87 (1994); page references
  to be added).
  - The polar form `polar hE x y = N(x + y) - N x - N y` of the norm is a non-degenerate symmetric
    `F`-bilinear form, so `ψ ∘ polar` is a self-dual bicharacter of `E`
    (`isSelfDualBicharacter_of_symm`), and `f = ψ ∘ N` is a character of second degree for it.
  - `gauss_integral_eventually_const`: for a character of second degree `f` of a self-dual
    bicharacter, the integrals of `f` over large compact open subgroups are constant (the integral
    of `f(x + m)` over `L` is the integral of `f` for `m` in a small subgroup `M`, and averaging over
    `M` reduces to the annihilator of `M`).
  - For `t = N w` a norm, the change of variables `z ↦ w z` scales Haar measure by `|t|⁻¹`
    (`map_mul_left_addHaar_algebra`, `HasGaussIntegral.comp_addEquiv`).
  - For `t` not a norm (`gauss_cancel`): the measure `n₁ + n_t` on `F`, with
    `n_a = |a| · (z ↦ a N z)_* μ`, is homogeneous of the degree of Haar measure, because
    multiplication by `u ∈ Fˣ` permutes `{n₁, n_t}` (norms have index two:
    `mul_mem_range_norm_of_finrank_eq_two`), and has no atom at `0`; so it is a multiple of Haar
    measure (`eq_smul_addHaar_of_map_mul_left`), and the integral of `ψ` over a large ball vanishes
    (`exists_setIntegral_setOf_valuation_le_eq_zero`). Hence the two Gauss integrals cancel:
    `γ(1) + |t| γ(t) = 0`.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, files under
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/`:
`GaussIntegralNormFormNonNormCancel.lean`, `GaussIntegralQuadraticCharEventuallyConst.lean`,
`GaussIntegralNormFormScaledEqSignAbsInv.lean` (each whole). The repository has no licence file;
the text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `GlobalTheory.KSp`, `KSp.Cancel`, `KSp.GaussNorm` →
  `Langlands.Theta.Unitary.Internal` (with `Cancel`, `GaussNorm` inside).
- Calls of the wrappers replaced by the wrapped lemmas, which are the Library's:
  `homogeneousMeasure_eq_smul_addHaar_localField` → `eq_smul_addHaar_of_map_mul_left`,
  `map_mul_left_eq_inv_norm_haarChar_smul` → `map_mul_left_addHaar_algebra`,
  `exists_integral_closedBall_addChar_eq_zero` → `exists_setIntegral_setOf_valuation_le_eq_zero`,
  `mul_mem_range_norm_of_not_mem` → `LocalClassField.mul_mem_range_norm_of_finrank_eq_two`,
  `isSelfDualBicharacterPairing_of_symmBilinForm` → `isSelfDualBicharacter_of_symm`,
  `hasGaussIntegral_comp_addEquiv_rescale` → `HasGaussIntegral.comp_addEquiv`.
- `SplitWeil.exists_isUnitVol` (a Haar measure with `vol(𝒪) = 1`) is replaced by Mathlib's
  `Measure.addHaar`, the normalization being unused; `Measure.map_smul` now asks for the
  measurability of the map, which is supplied.
- No `open scoped Classical` at file level; the two statements with `if` open it locally.

## Declarations

- `Langlands.Theta.isCharacterOfSecondDegree_mul_norm`, `Langlands.Theta.weilIndex_mul_norm`.

Internal (`Langlands.Theta.Unitary.Internal`): `Cancel.gauss_cancel`, `setIntegral_addSubgroup_add`,
`setIntegral_pair_char`, `gauss_integral_eventually_const`, `GaussNorm.polar` and its lemmas,
`hasGauss_norm_mul`.

## Dependencies

`Langlands.ClassFieldTheory.Local.QuadraticNormBall`, `Langlands.HarmonicAnalysis.QuadraticExtensionTopology`,
`Langlands.HarmonicAnalysis.LinearHaarScaling`, `Langlands.HarmonicAnalysis.Bicharacter.GaussIntegral`,
`Langlands.Theta.WeilIndex.Defs` (and through them `LinearHaarScaling`, `QuadraticNormIndex`, `Bicharacter.SelfDual`).
