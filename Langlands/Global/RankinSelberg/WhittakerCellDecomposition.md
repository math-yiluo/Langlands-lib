# Proof of the one-place Iwasawa cell decomposition of the Whittaker quotient measure

Module `Langlands.Global.RankinSelberg.WhittakerCellDecomposition`. The main theorem is

**`Langlands.Global.RankinSelbergGlobal.whittakerCellDecomposition :
WhittakerCellDecompositionStatement.{u}`**.

It proves the Library statement `WhittakerCellDecompositionStatement` exactly, at universe `u`,
with no extra hypotheses. The statement is in module
`Langlands.Global.RankinSelberg.WhittakerCellDecompositionStatement`. It covers every `m`
(including `m = 0`), every finite `S`, every finite place `v ∉ S`, every uniformizer `ϖ` and
every integrable `f`. The helper declarations live in namespace
`Langlands.Global.RankinSelbergGlobal.WhittakerCell`.

The measure theory comes from the Library module
`Langlands.Global.RankinSelberg.WhittakerQuotientScaling` (namespace
`…RankinSelbergGlobal.WhittakerQuotientScaling`). It defines the left translation
`leftShift F m a : q ↦ N_m(𝔸) (a · q.out)` and proves that for `a = ι_v(ϖ^λ)` it multiplies
`whittakerQuotientMeasure` by `N(v)^(-e(λ))`. The fact that `ι_v(ϖ^λ)` normalizes `N_m(𝔸)`
is `UnipotentConjugationModulus.conj_localPoint_torus_mem_iff`, from the Library module
`Langlands.Global.RankinSelberg.UnipotentConjugationModulus`. This file also imports
`Langlands.Automorphic.CuspidalL2.Basics` for `AdelicGL.finite_ofFinite`.

Write `μ = whittakerQuotientMeasure F m`, `U_S = unipotentIntegralClasses F m S`,
`N(v) = Ideal.absNorm v.asIdeal`, `e(λ) = modulusExponent lam = ∑_(i<j)(λ_i - λ_j)`, and
`T_λ = leftShift F m (localPoint F m v (torus ϖ lam))`.

## The proof

1. **The shift.** The statement's `shift lam` is, by definition, the Library's
   `leftShift F m (localPoint F m v (torus ϖ lam))`. The main theorem rewrites it so by `rfl`.
2. **The shift scales `μ`.** The Library's
   `WhittakerQuotientScaling.map_leftShift_localPoint_torus` gives
   `Measure.map T_λ μ = N(v)^(-e(λ)) • μ`. The statement's valuation `Valued.v` on `F_v` is,
   by definition, the valuation `WhittakerCellAdelicScaling.valuation F v` used there.
3. **The cells.** `cellShift m v ϖ lam` is the Library homeomorphism
   `WhittakerQuotientScaling.leftShiftHomeomorph` of `ι_v(ϖ^λ)`; as a function it is `T_λ`.
   `cell m S v ϖ lam = (cellShift m v ϖ lam).symm ⁻¹' U_S` is the image `C_λ = T_λ(U_S)`. It
   is measurable (`measurableSet_cell`). `cellShift_symm_apply` computes the inverse:
   `N_m(𝔸) g ↦ N_m(𝔸) ι_v(ϖ^λ)⁻¹ g`. The membership condition (`mem_cell_iff`, from
   `mk_localPoint_inv_mul_mem_iff`, for `v ∉ S`) is: `q ∈ C_λ` if and only if
   `q ∈ U_(insert v S)` and `ϖ^(-λ) (q.out)_v ∈ N_m(F_v) GL_m(𝒪_v)`. The proof uses
   the existing `LocalPointFactorization.finiteComponent_localPoint` and
   `LocalPointFactorization.finiteComponent_localPoint_of_ne`: `ι_v(t)` has
   component `t` at `v` and `1` at every other finite place.
4. **The cells partition `U_(insert v S)`.**
   - Existence (`exists_isUnipotentIntegral_torus_inv_mul`): every `x ∈ GL_m(F_v)` has some
     `λ` with `ϖ^(-λ) x ∈ N_m(F_v) GL_m(𝒪_v)`. For `m = n + 1` this is the Library's Iwasawa
     decomposition `GeneralLinear.Iwasawa.exists_iwasawa`, `x = u ϖ^λ k`. Then
     `ϖ^(-λ) x = (ϖ^(-λ) u ϖ^λ) k`, and the conjugate stays upper unipotent
     (`diagonalUnits_conj_mem_upperUnipotent`). For `m = 0` everything is trivial. The Library's
     `Conductor.integralSubgroup` and `FiniteAdelicGL.localIntegral` describe the same
     subgroup `GL_m(𝒪_v)` (`mem_localIntegral_iff_mem_integralSubgroup`).
   - Uniqueness (`eq_of_isUnipotentIntegral_torus_inv_mul`): if `ϖ^(-λ) x` and `ϖ^(-λ') x` are
     both in `N_m(F_v) GL_m(𝒪_v)`, then `λ = λ'`. Both equal the Library's
     `GeneralLinear.Iwasawa.exponent hϖ x`, by `GeneralLinear.Iwasawa.exponent_eq`. For
     `m = 0` there is only one `λ`.
   - Hence the cells are pairwise disjoint (`pairwise_disjoint_cell`), and their union is
     `U_(insert v S)` (`iUnion_cell`).
5. **Change of variables.**
   - `integrableOn_leftShift`: `f ∘ T_λ` is integrable on `U_S`. It is integrable on the
     whole quotient by the Library's `WhittakerQuotientScaling.integrable_comp_leftShift` and
     step 2. This is the first conclusion of the statement.
   - `absNorm_zpow_mul_setIntegral_leftShift`:
     `N(v)^(e(λ)) ∫_(U_S) f ∘ T_λ dμ = ∫_(C_λ) f dμ`. The Library's
     `WhittakerQuotientScaling.setIntegral_comp_leftShift` and step 2 give
     `∫_(U_S) f ∘ T_λ dμ = N(v)^(-e(λ)) ∫_(C_λ) f dμ`. Multiply by `N(v)^(e(λ))`; this uses
     `N(v) ≠ 0`, which holds because `v.asIdeal ≠ ⊥` (Mathlib's `Ideal.absNorm_eq_zero_iff`).
6. **Summation.** By step 5 the terms of the sum are `∫_(C_λ) f dμ`. Rewrite
   `U_(insert v S)` as `⋃_λ C_λ` (step 4). Mathlib's `hasSum_integral_iUnion` (countable
   family of pairwise disjoint measurable sets, `f` integrable on the union) gives the second
   conclusion of the statement.

## Other declarations

`isUnipotentIntegral_iff_exists` (membership in `N_m(F_v) GL_m(𝒪_v)` written with
`GeneralLinear.upperUnipotent`) and `localPoint_inv`. The file also declares local affine and
smooth instances for the `GL_m` group scheme, and opens `Classical` (for `insert v S`) and
`Function` (for `Disjoint on`).

## Provenance

The statement's Markdown gives the sources and explains why the statement's global one-place
form is internal. Cogdell's local unramified computation over `N_m(k) \ GL_m(k)` uses the
Iwasawa decomposition `h = n ϖ^J k` and `dh = dn δ_(B_m)^(−1)(ϖ^J) dk` (J. W. Cogdell,
*Lectures on L-functions, converse theorems, and functoriality for GL_n*, Fields lectures
2003, Lecture 7 §3, p.57). The proof follows the same idea. The Iwasawa decomposition at `v`
splits the classes by their `v`-component into cells indexed by `λ`. Translation by
`ι_v(ϖ^λ)` carries `U_S` onto the cell of `λ`. The image of `μ` under that translation is
`N(v)^(-e(λ)) μ = δ_B(ϖ^λ) μ`. So the integral over the cell carries the weight
`N(v)^(e(λ)) = δ_B^(−1)(ϖ^λ)`, which is Cogdell's factor. The Lean route is internal: the
scaling factor comes from the Library's `WhittakerQuotientScaling` (uniqueness of
right-invariant quotient measures and a Haar modulus computation on `N_m(𝔸)`), not from a
local product decomposition of the measure.
