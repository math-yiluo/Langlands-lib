import Langlands.Representation.Archimedean.ComplexGLTwoNoncompactPicture
import Langlands.Representation.Archimedean.ComplexJacquetFinite

/-!
# Operators on the `GL_2(ℂ)` principal series in the noncompact picture

For complex characters `d 0`, `d 1` let `X(d)` be the `U(2)`-finite functions of the standard
module of `List.ofFn d`, with the action `π` of `ℂ ⊗_ℝ 𝔤𝔩_2(ℂ)`, and let `φ_f(z) = f(w n(z))`.
We use the elements

* `D = (1 ⊗ E_01 - i ⊗ i E_01)/2` and `D̄ = (1 ⊗ E_01 + i ⊗ i E_01)/2`,
* `F = (1 ⊗ E_10 - i ⊗ i E_10)/2` and `F̄ = (1 ⊗ E_10 + i ⊗ i E_10)/2`,
* `H = 1 ⊗ i E_00`, `X₊ = D - F̄`, `X₋ = F - D̄` and `P = D + F̄`

of `ℂ ⊗_ℝ 𝔤𝔩_2(ℂ)`. In the noncompact picture they act by `∂`, `∂̄`,
`-z² ∂ - (p + 1) z`, `-z̄² ∂̄ - (q + 1) z̄`, `i l_1 - i z ∂ + i z̄ ∂̄`, and the resulting
combinations. `H` and `X₊` lie in the complexified Lie algebra of `U(2)`, so they preserve
every `U(2)`-stable subspace, and `[H, X₊] = i X₊`.

The noncompact picture is injective on the standard module: a function vanishing on all
`w n(z)` vanishes on the lower unipotent chart `1 + z E_10` for `z ≠ 0`, hence at `1` by
continuity, hence everywhere, because every `g` is `b` or `b w n(z)` with `b` upper triangular
(Bruhat decomposition).
Finally `w n(z) w = 1 + z E_10`, and `f(1 + z E_10) = φ_f(1/z) / δχ(diag(-z, 1/z))` for
`z ≠ 0`.
-/

noncomputable section

open scoped TensorProduct Matrix

open Complex ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace ComplexGLTwoNoncompact

variable (d : Fin 2 → ComplexCharacterData)

/-- The `U(2)`-finite principal series `X(d)`. -/
abbrev Xd : Submodule ℂ (Langlands.GeneralLinear 2 ℂ → ℂ) :=
  ComplexSwapJacquet.KFs 2 (List.ofFn d)

/-- The action of `ℂ ⊗_ℝ 𝔤𝔩_2(ℂ)` on `X(d)`. -/
abbrev πd : (ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ (Xd d) :=
  complexStandardLie 2 (List.ofFn d)

/-- The noncompact picture as a linear map on `X(d)`. -/
def ncpL : Xd d →ₗ[ℂ] (ℂ → ℂ) where
  toFun v := ncp v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ncpL_apply (v : Xd d) (z : ℂ) :
    ncpL d v z = (v : Langlands.GeneralLinear 2 ℂ → ℂ) (wn z) := rfl

theorem ncpL_eq (v : Xd d) : ncpL d v = ncp v := rfl

/-! ## The basic operators -/

section Basic

variable {d}

theorem tmul_eq_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem ncpL_tmul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) (v : Xd d) (z : ℂ) :
    ncpL d (πd d (c ⊗ₜ[ℝ] X) v) z = c * ncpL d (πd d ((1 : ℂ) ⊗ₜ[ℝ] X) v) z := by
  rw [tmul_eq_smul, map_smul, LinearMap.smul_apply, map_smul, Pi.smul_apply,
    smul_eq_mul]

theorem ncpL_single01 (v : Xd d) (c z : ℂ) :
    ncpL d (πd d ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single 0 1 c) v) z =
      c * dz (ncpL d v) z + conj c * dzb (ncpL d v) z := by
  rw [ncpL_apply, ComplexSwapJacquet.coe_lie]
  exact ncp_single01 (ComplexSwapJacquet.mem_of_mem_kFs v.2) c z

theorem ncpL_single10 (v : Xd d) (c z : ℂ) :
    ncpL d (πd d ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single 1 0 c) v) z =
      -c * (z ^ 2 * dz (ncpL d v) z + (pp d + 1) * z * ncpL d v z) -
        conj c * (conj z ^ 2 * dzb (ncpL d v) z + (qq d + 1) * conj z * ncpL d v z) := by
  rw [ncpL_apply, ComplexSwapJacquet.coe_lie]
  exact ncp_single10 (ComplexSwapJacquet.mem_of_mem_kFs v.2) c z

theorem ncpL_single00 (v : Xd d) (c z : ℂ) :
    ncpL d (πd d ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single 0 0 c) v) z =
      ComplexSwapJacquet.kappa (List.ofFn d) List.length_ofFn 1 c * ncpL d v z -
        (dz (ncpL d v) z * (c * z) + dzb (ncpL d v) z * conj (c * z)) := by
  rw [ncpL_apply, ComplexSwapJacquet.coe_lie]
  exact ncp_single00 (ComplexSwapJacquet.mem_of_mem_kFs v.2) c z

end Basic

/-- `D = (1 ⊗ E_01 - i ⊗ i E_01)/2`. -/
def eD : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) ⊗ₜ[ℝ] Matrix.single 0 1 1 - (I / 2) ⊗ₜ[ℝ] Matrix.single 0 1 I

/-- `D̄ = (1 ⊗ E_01 + i ⊗ i E_01)/2`. -/
def eDb : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) ⊗ₜ[ℝ] Matrix.single 0 1 1 + (I / 2) ⊗ₜ[ℝ] Matrix.single 0 1 I

/-- `F = (1 ⊗ E_10 - i ⊗ i E_10)/2`. -/
def eF : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) ⊗ₜ[ℝ] Matrix.single 1 0 1 - (I / 2) ⊗ₜ[ℝ] Matrix.single 1 0 I

/-- `F̄ = (1 ⊗ E_10 + i ⊗ i E_10)/2`. -/
def eFb : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) ⊗ₜ[ℝ] Matrix.single 1 0 1 + (I / 2) ⊗ₜ[ℝ] Matrix.single 1 0 I

/-- `H = 1 ⊗ i E_00`. -/
def eH : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ := (1 : ℂ) ⊗ₜ[ℝ] Matrix.single 0 0 I

/-- The raising operator `X₊ = D - F̄` of `𝔨_ℂ`. -/
def eXp : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ := eD - eFb

/-- The lowering operator `X₋ = F - D̄` of `𝔨_ℂ`. -/
def eXm : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ := eF - eDb

/-- `P = D + F̄`. -/
def eP : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ := eD + eFb

section Formulas

variable {d} (v : Xd d) (z : ℂ)

theorem ncpL_eD : ncpL d (πd d eD v) z = dz (ncpL d v) z := by
  rw [eD, map_sub, LinearMap.sub_apply, map_sub, Pi.sub_apply, ncpL_tmul (1 / 2), ncpL_tmul (I / 2),
    ncpL_single01, ncpL_single01]
  simp only [map_one, Complex.conj_I]
  linear_combination (-(dz (ncpL d v) z) / 2 + dzb (ncpL d v) z / 2) * Complex.I_sq

theorem ncpL_eDb : ncpL d (πd d eDb v) z = dzb (ncpL d v) z := by
  rw [eDb, map_add, LinearMap.add_apply, map_add, Pi.add_apply, ncpL_tmul (1 / 2), ncpL_tmul (I / 2),
    ncpL_single01, ncpL_single01]
  simp only [map_one, Complex.conj_I]
  linear_combination (dz (ncpL d v) z / 2 - dzb (ncpL d v) z / 2) * Complex.I_sq

theorem ncpL_eF : ncpL d (πd d eF v) z =
    -(z ^ 2 * dz (ncpL d v) z + (pp d + 1) * z * ncpL d v z) := by
  rw [eF, map_sub, LinearMap.sub_apply, map_sub, Pi.sub_apply, ncpL_tmul (1 / 2), ncpL_tmul (I / 2),
    ncpL_single10, ncpL_single10]
  simp only [map_one, Complex.conj_I]
  linear_combination
    ((z ^ 2 * dz (ncpL d v) z + (pp d + 1) * z * ncpL d v z) / 2 -
      (conj z ^ 2 * dzb (ncpL d v) z + (qq d + 1) * conj z * ncpL d v z) / 2) * Complex.I_sq

theorem ncpL_eFb : ncpL d (πd d eFb v) z =
    -(conj z ^ 2 * dzb (ncpL d v) z + (qq d + 1) * conj z * ncpL d v z) := by
  rw [eFb, map_add, LinearMap.add_apply, map_add, Pi.add_apply, ncpL_tmul (1 / 2), ncpL_tmul (I / 2),
    ncpL_single10, ncpL_single10]
  simp only [map_one, Complex.conj_I]
  linear_combination
    (-(z ^ 2 * dz (ncpL d v) z + (pp d + 1) * z * ncpL d v z) / 2 +
      (conj z ^ 2 * dzb (ncpL d v) z + (qq d + 1) * conj z * ncpL d v z) / 2) * Complex.I_sq

theorem kappa_one_I :
    ComplexSwapJacquet.kappa (List.ofFn d) List.length_ofFn 1 I = I * ((d 1).weight : ℂ) := by
  rw [kappa_ofFn, Complex.conj_I]
  simp only [Fin.val_one]
  push_cast
  ring

theorem ncpL_eH : ncpL d (πd d eH v) z =
    I * ((d 1).weight : ℂ) * ncpL d v z - I * z * dz (ncpL d v) z +
      I * conj z * dzb (ncpL d v) z := by
  rw [eH, ncpL_single00, kappa_one_I, map_mul, Complex.conj_I]
  ring

theorem ncpL_eXp : ncpL d (πd d eXp v) z =
    dz (ncpL d v) z + conj z ^ 2 * dzb (ncpL d v) z + (qq d + 1) * conj z * ncpL d v z := by
  rw [eXp, map_sub, LinearMap.sub_apply, map_sub, Pi.sub_apply, ncpL_eD, ncpL_eFb]
  ring

theorem ncpL_eXm : ncpL d (πd d eXm v) z =
    -(z ^ 2 * dz (ncpL d v) z + (pp d + 1) * z * ncpL d v z) - dzb (ncpL d v) z := by
  rw [eXm, map_sub, LinearMap.sub_apply, map_sub, Pi.sub_apply, ncpL_eF, ncpL_eDb]

theorem ncpL_eP : ncpL d (πd d eP v) z =
    dz (ncpL d v) z - (conj z ^ 2 * dzb (ncpL d v) z + (qq d + 1) * conj z * ncpL d v z) := by
  rw [eP, map_add, LinearMap.add_apply, map_add, Pi.add_apply, ncpL_eD, ncpL_eFb]
  ring

end Formulas

/-! ## The compact directions -/

section Compact

/-- `Y_0 = i E_00`. -/
def Y0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 0 I

/-- `Y_1 = E_01 - E_10`. -/
def Y1 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 1 1 - Matrix.single 1 0 1

/-- `Y_2 = i E_01 + i E_10`. -/
def Y2 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 1 I + Matrix.single 1 0 I

theorem star_Y0 : star Y0 = -Y0 := by
  rw [Y0, Matrix.star_eq_conjTranspose]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem star_Y1 : star Y1 = -Y1 := by
  rw [Y1, Matrix.star_eq_conjTranspose]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem star_Y2 : star Y2 = -Y2 := by
  rw [Y2, Matrix.star_eq_conjTranspose]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem eH_eq : eH = (1 : ℂ) ⊗ₜ[ℝ] Y0 := rfl

/-- `X₊ = (1 ⊗ Y_1 - i ⊗ Y_2)/2`. -/
theorem eXp_eq : eXp = (1 / 2 : ℂ) ⊗ₜ[ℝ] Y1 - (I / 2) ⊗ₜ[ℝ] Y2 := by
  rw [eXp, eD, eFb, Y1, Y2, TensorProduct.tmul_sub, TensorProduct.tmul_add]
  abel

variable {d}

/-- A `U(2)`-stable subspace of `X(d)` is stable under `H` and `X₊`. -/
theorem compact_stable (W : Submodule ℂ (Xd d))
    (hW : ∀ k, ∀ w ∈ W, complexStandardRep 2 (List.ofFn d) k w ∈ W) :
    (∀ w ∈ W, πd d eH w ∈ W) ∧ ∀ w ∈ W, πd d eXp w ∈ W := by
  have hgk := isComplexGKModule_complexStandardModule 2 (List.ofFn d)
  have hs := ComplexJacquetFinite.skew_stable hgk W hW
  refine ⟨fun w hw => hs Y0 star_Y0 w hw, fun w hw => ?_⟩
  rw [eXp_eq, map_sub, LinearMap.sub_apply, tmul_eq_smul, tmul_eq_smul (I / 2), map_smul,
    map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  exact W.sub_mem (W.smul_mem _ (hs Y1 star_Y1 w hw)) (W.smul_mem _ (hs Y2 star_Y2 w hw))

theorem lie_Y0_Y1 : Y0 * Y1 - Y1 * Y0 = Y2 := by
  rw [Y0, Y1, Y2]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.single_apply]

theorem lie_Y0_Y2 : Y0 * Y2 - Y2 * Y0 = -Y1 := by
  rw [Y0, Y1, Y2]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.single_apply]

/-- `[H, X₊] = i X₊`, applied to a vector. -/
theorem eH_eXp (v : Xd d) :
    πd d eH (πd d eXp v) = πd d eXp (πd d eH v) + I • πd d eXp v := by
  have h1 : ∀ w : Xd d, πd d ((1 : ℂ) ⊗ₜ[ℝ] Y0) (πd d ((1 : ℂ) ⊗ₜ[ℝ] Y1) w) =
      πd d ((1 : ℂ) ⊗ₜ[ℝ] Y1) (πd d ((1 : ℂ) ⊗ₜ[ℝ] Y0) w) + πd d ((1 : ℂ) ⊗ₜ[ℝ] Y2) w := by
    intro w
    have h := ComplexSwapJacquet.lie_comm (ds := List.ofFn d) Y0 Y1 w
    rwa [lie_Y0_Y1] at h
  have h2 : ∀ w : Xd d, πd d ((1 : ℂ) ⊗ₜ[ℝ] Y0) (πd d ((1 : ℂ) ⊗ₜ[ℝ] Y2) w) =
      πd d ((1 : ℂ) ⊗ₜ[ℝ] Y2) (πd d ((1 : ℂ) ⊗ₜ[ℝ] Y0) w) - πd d ((1 : ℂ) ⊗ₜ[ℝ] Y1) w := by
    intro w
    have h := ComplexSwapJacquet.lie_comm (ds := List.ofFn d) Y0 Y2 w
    rw [lie_Y0_Y2, TensorProduct.tmul_neg, map_neg, LinearMap.neg_apply] at h
    rw [h, sub_eq_add_neg]
  rw [eXp_eq, eH_eq, tmul_eq_smul (1 / 2) Y1, tmul_eq_smul (I / 2) Y2]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_sub]
  rw [h1, h2]
  match_scalars
  all_goals first
    | ring1
    | linear_combination (1 / 2 : ℂ) * Complex.I_sq

end Compact

/-! ## Injectivity of the noncompact picture -/

section Injective

variable {d}

theorem principalSeriesCharacter_ne_zero (a : Fin 2 → ℂˣ) :
    principalSeriesCharacter ℂ 2 (complexPositionCharacter (List.ofFn d)) a ≠ 0 := by
  rw [principalSeriesCharacter_ofFn]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => borelFactor_ne_zero _ _ (a j).ne_zero

/-- `f(1 + z E_10) = φ_f(1/z) / δχ(diag(-z, 1/z))` for `z ≠ 0`. -/
theorem apply_lowerChart {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (hf : f ∈ complexStandardModule 2 (List.ofFn d)) (z : ℂ) (hz : z ≠ 0) :
    f (ComplexSwapJacquet.lowerChart (0 : Fin 2) 1 hj01 z) =
      ncp f z⁻¹ / principalSeriesCharacter ℂ 2 (complexPositionCharacter (List.ofFn d))
        (ComplexSwapJacquet.chartTorus (0 : Fin 2) 1 (Units.mk0 z⁻¹ (inv_ne_zero hz))) := by
  have h := ComplexSwapJacquet.apply_chart_eq hf (0 : Fin 2) 1 hj01 z⁻¹ (inv_ne_zero hz)
  rw [inv_inv] at h
  rw [ncp, h, mul_div_cancel_left₀ _ (principalSeriesCharacter_ne_zero _)]

/-- If `φ_f = 0` then `f = 0`. -/
theorem eq_zero_of_ncp_eq_zero {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (hf : f ∈ complexStandardModule 2 (List.ofFn d)) (h0 : ∀ z, ncp f z = 0) : f = 0 := by
  have hlow : ∀ z, z ≠ 0 → f (ComplexSwapJacquet.lowerChart (0 : Fin 2) 1 hj01 z) = 0 := by
    intro z hz
    rw [apply_lowerChart hf z hz, h0, zero_div]
  have hcont : Continuous fun z => f (ComplexSwapJacquet.lowerChart (0 : Fin 2) 1 hj01 z) :=
    (ComplexSwapJacquet.contDiff_apply_lowerChart hf.1 0 1 hj01).continuous
  have h1 : f 1 = 0 := by
    have hlim : Filter.Tendsto (fun z => f (ComplexSwapJacquet.lowerChart (0 : Fin 2) 1 hj01 z))
        (nhdsWithin 0 {0}ᶜ) (nhds (f (ComplexSwapJacquet.lowerChart (0 : Fin 2) 1 hj01 0))) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : (fun z => f (ComplexSwapJacquet.lowerChart (0 : Fin 2) 1 hj01 z)) =ᶠ[nhdsWithin 0 {0}ᶜ]
        fun _ => 0 := eventually_nhdsWithin_of_forall fun z hz => hlow z hz
    rw [ComplexSwapJacquet.lowerChart_zero] at hlim
    exact tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  funext g
  set M : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have hdet : M.det ≠ 0 := by
    rw [hM]
    exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit |>.ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases h10 : M 1 0 = 0
  · have h00 : M 0 0 ≠ 0 := by
      intro h; apply hdet; rw [h, h10]; ring
    have h11 : M 1 1 ≠ 0 := by
      intro h; apply hdet; rw [h, h10]; ring
    have hg : g = Iwasawa.diagonalUnits ![Units.mk0 (M 0 0) h00, Units.mk0 (M 1 1) h11] *
        ((ComplexSwapJacquet.chartUnipotent (0 : Fin 2) 1 hj01 (-(M 0 1 / M 0 0)) :
          upperUnipotent 2 ℂ) : Langlands.GeneralLinear 2 ℂ) * 1 := by
      apply Units.ext
      rw [mul_one, Units.val_mul, Iwasawa.diagonalUnits_val]
      change M = _ * Matrix.transvection 0 1 (-(-(M 0 1 / M 0 0)))
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection, Matrix.single_apply, h10]
      field_simp
    rw [hg, hf.2, h1, mul_zero, Pi.zero_apply]
  · set a : ℂ := M 0 1 - M 0 0 * M 1 1 / M 1 0 with ha_def
    have haM : a * M 1 0 = -(M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
      rw [ha_def, sub_mul, div_mul_cancel₀ _ h10]; ring
    have ha : a ≠ 0 := by
      intro h; apply hdet; rw [h, zero_mul] at haM; linear_combination haM
    have hg : g = Iwasawa.diagonalUnits ![Units.mk0 a ha, Units.mk0 (M 1 0) h10] *
        ((ComplexSwapJacquet.chartUnipotent (0 : Fin 2) 1 hj01 (-(M 0 0 / a)) :
          upperUnipotent 2 ℂ) : Langlands.GeneralLinear 2 ℂ) * wn (M 1 1 / M 1 0) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val, wn_val]
      change M = _ * Matrix.transvection 0 1 _ * _
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection, Matrix.single_apply]
      all_goals (try field_simp)
      linear_combination -haM
    rw [hg, hf.2]
    have := h0 (M 1 1 / M 1 0)
    rw [ncp] at this
    rw [this, mul_zero, Pi.zero_apply]

/-- The noncompact picture is injective on `X(d)`. -/
theorem ncpL_injective : Function.Injective (ncpL d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  apply Subtype.ext
  exact eq_zero_of_ncp_eq_zero (ComplexSwapJacquet.mem_of_mem_kFs v.2)
    fun z => congrFun hv z

end Injective

/-! ## The Weyl element -/

section Weyl

/-- The Weyl element `w` as a unitary matrix. -/
def wU : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem toUnits_wU : (Unitary.toUnits wU : Langlands.GeneralLinear 2 ℂ) = complexGLTwoWeyl := by
  apply Units.ext
  rfl

/-- `w n(z) w = 1 + z E_10`. -/
theorem wn_mul_weyl (z : ℂ) :
    wn z * complexGLTwoWeyl = ComplexSwapJacquet.lowerChart (0 : Fin 2) 1 hj01 z := by
  apply Units.ext
  rw [Units.val_mul, wn_val]
  change _ = Matrix.transvection 1 0 z
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [complexGLTwoWeyl, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection]

variable {d}

/-- `φ_{ρ(w) f}(z) = f(1 + z E_10)`. -/
theorem ncpL_rho_wU (v : Xd d) (z : ℂ) :
    ncpL d (complexStandardRep 2 (List.ofFn d) wU v) z =
      (v : Langlands.GeneralLinear 2 ℂ → ℂ) (ComplexSwapJacquet.lowerChart (0 : Fin 2) 1 hj01 z) := by
  rw [ncpL_apply, principalSeriesRep_apply_coe, ← wn_mul_weyl, ← toUnits_wU]
  rfl

end Weyl

end ComplexGLTwoNoncompact

end Langlands.Archimedean
