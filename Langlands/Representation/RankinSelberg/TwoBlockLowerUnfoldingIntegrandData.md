# The integrand of the Section 4.7 lower unfolding

Module `Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData`,
namespace `Langlands.RankinSelberg.TwoBlockLowerUnfolding`.

Author: Worker 1037.

This module is a definitions unit for the right side of JPSS (1983), Section
4.7, equation (1). It constructs the actual unweighted scalar function

```text
[g] ↦ W(C g) f[g; e, e] (gΦ)~[ζ, η]
```

on the published quotient `H⁻ \ GL_(t+1)`, where `C = w'` and `H⁻ = H_(t_1,t_2)`.
The selected definition is
`Langlands.RankinSelberg.TwoBlockLowerUnfolding.integrand`. The module also
constructs the partial Fourier value `g ↦ (gΦ)~[ζ, η]`, proves its explicit
formula, and proves that its inner integrand is absolutely integrable. It
proves the three covariance laws under `H⁻` and their cancellation. The source
states none of these as a numbered result; they are internal data for the
displayed integral. The weight `|det g|^s`, outer measurability, outer
integrability and the identity (4.7)(1) are not part of this module.

## Source and conventions

Source: Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*
(1983), source ID `jpss-1983-rankin-selberg`, Section (4.7). The printed pages
412–413 are zero-based PDF indices 46–47, which were inspected visually. No
errata note for this source is registered in the project literature.

- On printed page 412, the right side of equation (1) of (4.7) is, up to the
  factor `L(1 - s, π^ι × σ_1^ι)⁻¹ ω_(σ_1)(-1)^(r-1)`, the integral over
  `H_(t_1,t_2) \ G_r` of

  ```text
  f[g; e, e] W[w_r (w_(t_1) 0; 0 w_(t_2)) g] |det g|^s (gΦ)~[ζ_(t_1), η_(t_2)] dg.
  ```

- On printed page 413, `H_(t_1,t_2)` is the unipotent subgroup of `G_r` of all
  matrices `(n_1 0; x n_2)` with `n_i ∈ N_(t_i)`. The rows are
  `ζ_(t_1) = (1, 0, …, 0) ∈ F^(t_1)` and `η_(t_2) = (0, …, 0, 1) ∈ F^(t_2)`.
  The partial Fourier transform is
  `Φ~(ξ, v) = ∫_(F^(t_1)) Φ[(w, v)] ψ(ξ ᵗw) dw` for `ξ, w ∈ F^(t_1)` and
  `v ∈ F^(t_2)`. Here `r = t = t_1 + t_2`.

The correspondence with this module is as follows.

| JPSS | Here |
| --- | --- |
| block ranks `t_1`, `t_2` | `a = m 0 + 1`, `b = m 1 + 1` |
| total rank `r = t_1 + t_2` | `t + 1`, with `h : ∑ i, (m i + 1) = t + 1` |
| `G_r` | `GeneralLinear (t + 1) F.Carrier` |
| `w' = w_r diag(w_(t_1), w_(t_2))` | the published `TwoBlockLowerUnipotentQuotient.blockRotation h F.Carrier` |
| `H_(t_1,t_2)` | the published `TwoBlockLowerUnipotentQuotient.lowerBlockUnipotent h F.Carrier` |
| `H_(t_1,t_2) \ G_r` | the published `TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier` |
| `(n_1, n_2)` for `(n_1 0; x n_2)` | the published `TwoBlockLowerUnipotentQuotient.diagonalBlocks h F.Carrier u` |
| the row `(w, v)` | `TwoBlockRowPartialFourier.join (succBlockEquiv h) w v` |
| `ζ_(t_1)`, `η_(t_2)` | `zeta (m 0)`, `eta (m 1)` |
| `gΦ`, that is `x ↦ Φ(x g)` | `HarmonicAnalysis.rowTranslate g Φ` |
| `Φ~(ξ, v)` | `TwoBlockRowPartialFourier.rowPartialFourierIntegral ψ μ (succBlockEquiv h) Φ ξ v` |
| `(gΦ)~[ζ, η]` | `partialSection h ψ μ Φ g` |
| `W ∈ W(π; ψ)` | `Wtest : RankinSelberg.WhittakerFunctions ψ t` |
| `f`, a section of (4.6.1) | `f : TwoBlockJacquet.Sections F h σ` |
| `f[g; e, e]` | `TwoBlockJacquet.scalarSection (fun i => (ell i).val) f g 1` |
| the integrand without `|det g|^s` | `groupIntegrand ell f Wtest Φ μ g`, and `integrand ell f Wtest Φ μ [g]` |

`succBlockEquiv h` is the published contiguous placement: block `0` occupies
positions `0, …, a - 1` and block `1` positions `a, …, t`, matching the source
row `(w, v)`. As in the Section 4.6 module
`TwoBlockUnfoldingIntegrandData`, the source's evaluation of the two
`ψ̄`-Whittaker functions at the identity is replaced by arbitrary actual
inverse-character forms `ell i : Whittaker.glInverseFunctionals ψ (m i) (σ i)`.
The scalar section contracts `f(g)` with `ℓ_0 ⊗ ℓ_1` at the Levi identity `1`,
which is the source's `(e, e)`.

## Hypotheses and generalizations

Throughout, `p` is a prime and `F : PadicField.{uF} p` is a canonical `p`-adic
field with its canonical topology `F.canonicalTopologicalData.topology`. The
block carriers `W i : Type uW` live in their own universe `uW`; the
representations `σ i` of `GeneralLinear (m i + 1) F.Carrier` are arbitrary. The
block ranks are arbitrary positive numbers: either may be one, and they need
not be equal.

- `ψ` is any `HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`. No
  self-duality is used, and no proof uses the nontriviality field.
- `μ` is any supplied `HarmonicAnalysis.AdditiveHaarMeasure F.Carrier`; no
  measure is chosen or rescaled. The source integrates against the self-dual
  `dw`; any Haar measure is allowed here. The task allowed the premise
  `SigmaFinite μ.measure`, but it is not needed:
  `sigmaFinite_additiveHaarMeasure μ` proves it, because `F` is second
  countable and an additive Haar measure is locally finite.
- The measurable structure is any `[MeasurableSpace F.Carrier]`. The
  definitions `partialSection` and `groupIntegrand` need nothing more. The
  integrability, the measure preservation, the invariance and the descended
  `integrand` assume
  `[@BorelSpace F.Carrier F.canonicalTopologicalData.topology _]`, which says
  that it is the Borel structure of the canonical topology.
- `ell i` are any elements of the inverse-character spaces, and `f` is any
  section of the published lower normalized induction. Zero forms and zero
  sections are allowed. No smoothness, irreducibility, full Whittaker type or
  nonvanishing is assumed.
- `Wtest` is any element of `RankinSelberg.WhittakerFunctions ψ t`, that is,
  any function with `W(n g) = θ(n) W(g)` for `n ∈ N_(t+1)`. This generalizes the
  source's Whittaker function of `π`. Only this covariance is used: no local
  constancy and no membership in a Whittaker model.
- `Φ` is any element of `HarmonicAnalysis.SchwartzBruhat (Fin (t + 1) → F.Carrier)`.

## The rows `ζ` and `η` (section `Rows`)

No equal row objects exist in the Library, so the rows are defined explicitly
over any type with `0` and `1`:

- `zeta n i = if i = 0 then 1 else 0` and
  `eta n j = if j = Fin.last n then 1 else 0`, rows of length `n + 1`, with
  `zeta_apply` and `eta_apply`.
- `rowPairing_zeta`: `rowPairing w (zeta n) = w 0`. So the source's
  `ψ(ζ ᵗw)` is `ψ(w_0)`.
- `vecMul_eta`: `η M` is the last row of `M`.
- `vecMul_upperUnipotent_zero` and `rowPairing_vecMul_upperUnipotent_zeta`:
  right multiplication by an upper unipotent matrix does not change the first
  coordinate of a row, nor its pairing with `ζ`.

## The row action of `H⁻` (section `RowAction`)

This section works over any commutative ring `R`.

- `corner h u` is the entry of `u` in row `B.index 1 (Fin.last (m 1))` and
  column `B.index 0 0`, with `B = succBlockShape m h`. It is the corner entry
  of the task, and the entry in the published `lowerCharacter_eq_diagonalBlocks`.
  `corner_def` unfolds it.
- `cornerRow h u` is the last row `η X` of the lower-left block `X` of `u`:
  its coordinate `a` is the entry in row `B.index 1 (Fin.last (m 1))` and
  column `B.index 0 a`. `cornerRow_zero` says its first coordinate is the
  corner.
- `vecMul_join_eta h u w`: for `u = (n_a 0; X n_b) ∈ H⁻`,

  ```text
  vecMul (join e w η) u = join e (vecMul w (diagonalBlocks h R u 0) + cornerRow h u) η.
  ```

  The proof splits the row sum into the two blocks. The block-`0` rows give
  `w n_a` and the first block of the result. The block-`1` rows contribute only
  the row of `η`'s last coordinate, which is `cornerRow` in the first block.
  In the second block, the zero upper-right block of `u`
  (`index_zero_one_eq_zero`) and the unipotence of `n_b` (from
  `mem_lowerBlockUnipotent_iff`) leave the last row of `n_b`, which is `η`.

## Covariance of the scalar section and of `W(C ·)` (section `Covariance`)

- `scalarSection_lowerBlockUnipotent_mul ell f u g` is law 1:

  ```text
  scalarSection (fun i => (ell i).val) f (u.val * g) 1 =
    (∏ i, (inverseStandardCharacter ψ (m i) (diagonalBlocks h F.Carrier u i) : ℂ)) *
      scalarSection (fun i => (ell i).val) f g 1
  ```

  It holds for every `u ∈ H⁻`, with arbitrary lower-left rectangle. The proof
  includes `u` into the published opposite parabolic
  (`lowerBlockUnipotent_le_oppositeParabolic`) and takes its opposite Levi
  projection `b`, which is `diagonalBlocks h F.Carrier u` by definition. The
  published `scalarSection_covariant` gives the factor of the half modulus of
  `b` and moves `b` to the Levi argument. The half modulus is one by
  `leviHalfModulus_eq_one`, `leviModulus_eq_one` and
  `determinantNorm_eq_one_of_mem_upperUnipotent`, because both diagonal blocks
  are upper unipotent. The published `tensorContraction_blockTensor` then
  extracts the two inverse block characters. In rank-one blocks these
  characters are `1`.
- `whittaker_blockRotation_lowerBlockUnipotent_mul Wtest u g` is law 3:

  ```text
  Wtest.val (C * (u.val * g)) = (lowerCharacter h ψ u : ℂ) * Wtest.val (C * g)
  ```

  with `C = blockRotation h F.Carrier`. Since
  `C u = (C u C⁻¹) C = (conjugationEquiv h F.Carrier u).val C`
  (`conjugationEquiv_apply_val`), the covariance of `Wtest` under the upper
  unipotent element `conjugationEquiv h F.Carrier u` gives this. Its character
  value is `lowerCharacter h ψ u` by definition.

## The partial Fourier value (sections `PartialSection` and `Integrability`)

- `isTopologicalRing_carrier F`: the canonical topology makes `F.Carrier` a
  topological ring. `sigmaFinite_additiveHaarMeasure μ` proves the σ-finiteness
  described above.
- `partialSection h ψ μ Φ g` is defined with the exact value

  ```text
  rowPartialFourierIntegral ψ μ (succBlockEquiv h) (rowTranslate g Φ) (zeta (m 0)) (eta (m 1))
  ```

  (`partialSection_def`). The task wrote `partialSection ψ μ Φ g`. The proof
  `h` of the rank decomposition is an explicit first argument because nothing
  else in the arguments determines `m` and `h`.
- `partialSection_apply` is the explicit formula

  ```text
  partialSection h ψ μ Φ g =
    ∫ w, ψ.complex (w 0) * Φ (vecMul (join (succBlockEquiv h) w (eta (m 1))) g.val)
      ∂rowMeasure μ (m 0 + 1).
  ```

  This is the source's integral with the plus sign `ψ(ζ ᵗw) = ψ(w_0)`. It
  integrates over the first block only.
- `partialSection_integrable h ψ μ Φ g`: for every `g`, this inner integrand is
  integrable for the supplied `rowMeasure μ (m 0 + 1)`. The proof applies the
  published `rowPartialFourierIntegrand_integrable` to the Schwartz–Bruhat
  function `rowTranslate g Φ`. It uses `rowTranslate_apply` and
  `rowPairing_zeta`, together with the facts that `F` is Hausdorff and totally
  disconnected.
- `rowMeasure_map_vecMul_upperUnipotent μ n`: right multiplication
  `x ↦ x n` by an upper unipotent `n` preserves `rowMeasure μ d`. The published
  `rowMeasure_map_vecMul` scales by `|det n|⁻¹`, with the scalar Haar scaling
  `padicScalarHaarScaling` and the normalized absolute value. Here `det n = 1`
  by `RankinSelberg.unipotent_det`.
- `partialSection_lowerBlockUnipotent_mul h ψ μ Φ u g` is law 2:

  ```text
  partialSection h ψ μ Φ (u.val * g) = ψ.complex (-corner h u) * partialSection h ψ μ Φ g
  ```

  It is derived for the actual row action and the supplied Haar measure. Write
  `φ = rowTranslate g Φ` and `n_a = diagonalBlocks h F.Carrier u 0`. By
  `rowTranslate_mul` and `vecMul_join_eta`, the integrand at `w` is
  `ψ(w_0) φ(join e (w n_a + η X) η)`. Since `(w n_a)_0 = w_0`, it is the
  function `x ↦ ψ(x_0) φ(join e (x + η X) η)` at `x = w n_a`. The change of
  variables `w ↦ w n_a` is measure preserving and a measurable embedding
  (`rowHomeomorph`), so `MeasurePreserving.integral_comp` removes it. The
  published `integral_join_add` turns the translation by `η X` into the factor
  `ψ(-⟨η X, ζ⟩) = ψ(-corner)`. No integrability hypothesis enters.

## The scalar function and its descent (section `Integrand`)

- `groupIntegrand ell f Wtest Φ μ g` is

  ```text
  Wtest.val (blockRotation h F.Carrier * g) *
    TwoBlockJacquet.scalarSection (fun i => (ell i).val) f g 1 *
    partialSection h ψ μ Φ g
  ```

  (`groupIntegrand_def`). The data `h` is inferred from `f`.
- `groupIntegrand_lowerBlockUnipotent_mul ell f Wtest Φ μ u g`: for every
  `u ∈ H⁻` and every `g`,
  `groupIntegrand ell f Wtest Φ μ (u.val * g) = groupIntegrand ell f Wtest Φ μ g`.
  The proof rewrites by laws 3, 1 and 2 and expands the lower character by the
  published `lowerCharacter_eq_diagonalBlocks` as
  `θ_a(n_a) θ_b(n_b) ψ(corner)`. Then `θ_i(n_i) θ_i(n_i)⁻¹ = 1` (`Units.mul_inv`)
  and `ψ(corner) ψ(-corner) = 1` cancel all factors.
- `integrand ell f Wtest Φ μ : LowerQuotient h F.Carrier → ℂ` is the published
  `QuotientIntegration.descend` of `groupIntegrand` along this invariance. No
  coset representative is chosen.
- `integrand_mk` (a `simp` lemma) is the representative formula at every
  `[g] = Quotient.mk _ g`. Its right side is the group value
  `Wtest.val (blockRotation h F.Carrier * g) * scalarSection (fun i => (ell i).val) f g 1 *
  partialSection h ψ μ Φ g`. `integrand_mk_eq_groupIntegrand` states the same
  with `groupIntegrand`. Both hold by `rfl`.

## The weight `|det g|^s`

The source integrand also contains `|det g|^s`. Every element of `H⁻` is
block lower triangular with unipotent diagonal blocks, so it has
determinant one (the published
`TwoBlockLowerUnipotentQuotient.determinant_eq_one_of_mem_lowerBlockUnipotent`).
Hence `|det (u g)|^s = |det g|^s`, and the weight is a function on
`H⁻ \ GL_(t+1)`. It is constant on each published slice
`TwoBlockLowerUnipotentQuotient.determinantSlice F h k` of the determinant order
`determinantOrder F h [g] = ord (det g)`, the source's `H_(t_1,t_2) \ G_r^m`.
A later Mellin unit supplies this weight. This module constructs
only the unweighted coefficient function. It does not assert the complete
weighted integral, its convergence or the identity (4.7)(1).
