import Langlands.Global.RankinSelberg.UnfoldingDualGL
import Langlands.Global.RankinSelberg.UnfoldingOrdinary
import Langlands.Global.RankinSelberg.UnequalUnfoldingStatement

/-! # The dual unfolding of unequal-rank global integrals, from a dual Whittaker expansion -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global

local instance unfoldingDualSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unfoldingDualSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

local instance unfoldingDualRectangleMeasurableSpace (F : Type u) [Field F] [NumberField F]
    (k m : ℕ) : MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance unfoldingDualRectangleBorelSpace (F : Type u) [Field F] [NumberField F]
    (k m : ℕ) : BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance unfoldingDualBlockLocallyCompact (F : Type u) [Field F] [NumberField F]
    {a b n : ℕ} (h : a + b = n) :
    LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F h)) :=
  (GeneralLinearBlockUnipotent.isClosed_adelicPoints F h).locallyCompactSpace

local instance unfoldingDualUnipotentLocallyCompact (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

section Rectangle

variable (F : Type u) [Field F] [NumberField F]

instance rectangleMeasure_sFinite (k m : ℕ) : SFinite (rectangleMeasure F k m) := by
  unfold rectangleMeasure GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure
    AdelicSubgroupPoints.normalizedHaarMeasure
  infer_instance

/-- Reindexing invertible adelic matrices is continuous. -/
theorem continuous_reindexGL {k l : ℕ} (e : Fin k ≃ Fin l) :
    Continuous (GeneralLinear.reindex (R := Adeles F) e) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun g : Matrix.GeneralLinearGroup (Fin k) (Adeles F) =>
      Matrix.reindex e e (g : Matrix (Fin k) (Fin k) (Adeles F))
    exact Units.continuous_val.matrix_reindex _ _
  · change Continuous fun g : Matrix.GeneralLinearGroup (Fin k) (Adeles F) =>
      Matrix.reindex e e (↑g⁻¹ : Matrix (Fin k) (Fin k) (Adeles F))
    exact Units.continuous_coe_inv.matrix_reindex _ _

theorem continuous_rectangularPoint {r t : ℕ} (h : t < r) :
    Continuous (fun p : Points F (t + 1) × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F) =>
      rectangularPoint F h p.1 p.2) := by
  have he : Continuous (GeneralLinearGroupPoints.adelicEquiv F (t + 1)) :=
    (GeneralLinearGroupPoints.adelicHomeomorph F (t + 1)).continuous
  have h0 : Continuous (fun p : Points F (t + 1) ×
      Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F) =>
        ((GeneralLinearGroupPoints.adelicEquiv F (t + 1) p.1, p.2,
          (1 : GeneralLinear.lowerTriangularSubgroup (r - (t + 1)) (Adeles F))) :
          GeneralLinear.LowerBlockParameters (t + 1) (r - (t + 1)) (Adeles F))) :=
    (he.comp continuous_fst).prodMk (continuous_snd.prodMk continuous_const)
  have h1 := (GeneralLinear.continuous_lowerBlockLocalization (a := t + 1) (d := r - (t + 1))
    (R := Adeles F) 1).comp h0
  exact (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm.continuous.comp
    ((continuous_reindexGL F _).comp h1)

/-- `∫_x W(rect(g, x)) dx` over the rectangular matrices. -/
def dualRectIntegral {r t : ℕ} (h : t < r) (W : Points F (r + 1) → ℂ) (g : Points F (t + 1)) :
    ℂ :=
  ∫ x, W (rectangularPoint F h g x) ∂rectangleMeasure F (r - (t + 1)) (t + 1)

theorem measurable_dualRectIntegral {r t : ℕ} (h : t < r) {W : Points F (r + 1) → ℂ}
    (hW : Measurable W) : Measurable (dualRectIntegral F h W) := by
  have hm : Measurable (fun p : Points F (t + 1) ×
      Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F) => W (rectangularPoint F h p.1 p.2)) :=
    hW.comp (continuous_rectangularPoint F h).measurable
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_dualRectNormIntegral {r t : ℕ} (h : t < r) {W : Points F (r + 1) → ℂ}
    (hW : Measurable W) :
    Measurable (fun g : Points F (t + 1) => ∫ x, ‖W (rectangularPoint F h g x)‖
      ∂rectangleMeasure F (r - (t + 1)) (t + 1)) := by
  have hm : Measurable (fun p : Points F (t + 1) ×
      Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F) =>
        ‖W (rectangularPoint F h p.1 p.2)‖) :=
    (hW.comp (continuous_rectangularPoint F h).measurable).norm
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end Rectangle

section DualWhittaker

variable (F : Type u) [Field F] [NumberField F]

/-- The generic character of `ψ⁻¹` is the inverse of that of `ψ`. -/
theorem genericCharacter_inv_eq_inv (r : ℕ) (ψ : AddChar (Adeles F) ℂ) (m : Fin r → F)
    (x : unipotentAdelic F (r + 1)) :
    genericCharacter F r ψ⁻¹ m x = (genericCharacter F r ψ m x)⁻¹ := by
  simp only [genericCharacter]
  rw [AddChar.inv_apply']

theorem genericCharacter_ne_zero (r : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (m : Fin r → F) (x : unipotentAdelic F (r + 1)) :
    genericCharacter F r ψ m x ≠ 0 := by
  intro h0
  have := norm_genericCharacter F r ψ hψ.2.2.2 m x
  rw [h0, norm_zero] at this
  exact zero_ne_one this

variable [CompactSpace (AdeleQuotient F)]

/-- The dualized and Weyl-translated Whittaker function `g ↦ W(w ᵗ(g w')⁻¹)`. -/
abbrev dualWhittaker {r t : ℕ} (h : t < r) (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (v : T.Space) : Points F (r + 1) → ℂ :=
  translateFunction F (r + 1) (unfoldingWeyl F h) (dualFunction F (r + 1) (cuspWhittaker F T ψ v))

theorem measurable_dualWhittaker {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) :
    Measurable (dualWhittaker F h T ψ v) :=
  (measurable_cuspWhittaker F T ψ hψ v).comp
    ((continuous_dualPoint F (r + 1)).comp (continuous_id.mul continuous_const)).measurable

/-- Left translation by `diag(n, I)` multiplies the dual Whittaker function by the inverse
character. -/
theorem dualWhittaker_pad_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (n : unipotentAdelic F (t + 1))
    (y : Points F (r + 1)) :
    dualWhittaker F h T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) (n : Points F (t + 1)) * y) =
      (genericCharacter F t ψ (fun _ => 1) n)⁻¹ * dualWhittaker F h T ψ v y := by
  simp only [dualWhittaker, translateFunction, dualFunction_eq]
  have hp : pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) (n : Points F (t + 1)) =
      (padUnipotent F (Nat.le_of_lt (Nat.succ_lt_succ h)) n : Points F (r + 1)) := rfl
  rw [mul_assoc, dualPoint_mul, hp, ← coe_dualConjUnipotent,
    cuspWhittaker_mul_left F T ψ hψ v, genericCharacter_dualConjUnipotent,
    genericCharacter_padUnipotent]

/-- The rectangular integral transforms by the inverse character under `N_m(𝔸)`. -/
theorem dualRectIntegral_unipotent_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (n : unipotentAdelic F (t + 1))
    (g : Points F (t + 1)) :
    dualRectIntegral F h (dualWhittaker F h T ψ v) ((n : Points F (t + 1)) * g) =
      (genericCharacter F t ψ (fun _ => 1) n)⁻¹ *
        dualRectIntegral F h (dualWhittaker F h T ψ v) g := by
  unfold dualRectIntegral
  simp_rw [rectangularPoint_mul_left, dualWhittaker_pad_mul F h T ψ hψ v]
  exact integral_const_mul _ _

/-- The norm integral is invariant under `N_m(𝔸)`. -/
theorem dualRectNormIntegral_unipotent_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (n : unipotentAdelic F (t + 1))
    (g : Points F (t + 1)) :
    ∫ x, ‖dualWhittaker F h T ψ v (rectangularPoint F h ((n : Points F (t + 1)) * g) x)‖
        ∂rectangleMeasure F (r - (t + 1)) (t + 1) =
      ∫ x, ‖dualWhittaker F h T ψ v (rectangularPoint F h g x)‖
        ∂rectangleMeasure F (r - (t + 1)) (t + 1) := by
  simp_rw [rectangularPoint_mul_left, dualWhittaker_pad_mul F h T ψ hψ v, norm_mul, norm_inv,
    norm_genericCharacter F t ψ hψ.2.2.2, inv_one, one_mul]

/-- The dual of the `ψ⁻¹`-Whittaker function transforms by the character of `ψ`. -/
theorem dualCuspWhittaker_unipotent_mul {t : ℕ}
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v' : T'.Space) (n : unipotentAdelic F (t + 1))
    (g : Points F (t + 1)) :
    dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v') ((n : Points F (t + 1)) * g) =
      genericCharacter F t ψ (fun _ => 1) n *
        dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v') g := by
  simp only [dualFunction_eq]
  rw [dualPoint_mul, ← coe_dualConjUnipotent,
    cuspWhittaker_mul_left F T' ψ⁻¹ (isStandardAdditiveCharacter_inv F ψ hψ) v',
    genericCharacter_dualConjUnipotent, genericCharacter_inv_eq_inv, inv_inv]

theorem measurable_dualCuspWhittaker {t : ℕ}
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v' : T'.Space) :
    Measurable (dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v')) :=
  (measurable_cuspWhittaker F T' ψ⁻¹ (isStandardAdditiveCharacter_inv F ψ hψ) v').comp
    (continuous_dualPoint F (t + 1)).measurable

theorem continuous_dualCuspFunction {t : ℕ} (T' : Automorphic.CuspidalOperatorRealization F t)
    (v' : T'.Space) : Continuous (dualFunction F (t + 1) (cuspFunction F T' v')) :=
  (continuous_cuspFunction F T' v').comp (continuous_dualPoint F (t + 1))

theorem dualCuspFunction_rational_mul {t : ℕ}
    (T' : Automorphic.CuspidalOperatorRealization F t) (v' : T'.Space) {k : Points F (t + 1)}
    (hk : k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1))) (x : Points F (t + 1)) :
    dualFunction F (t + 1) (cuspFunction F T' v') (k * x) =
      dualFunction F (t + 1) (cuspFunction F T' v') x := by
  simp only [dualFunction_eq]
  rw [dualPoint_mul, cuspFunction_rational_mul F T' v' (dualConj_mem_rationalSubgroup F _ hk)]

/-- The dual of the `ψ⁻¹`-Whittaker function of `φ'` is the `ψ`-coefficient of the dual cusp
form, written over the fundamental domain of `N_m(F)` in `N_m(𝔸)`; the twist preserves the
measure. -/
theorem dualCuspWhittaker_eq_setIntegral {t : ℕ}
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v' : T'.Space) (x : Points F (t + 1)) :
    dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v') x =
      ((AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F (t + 1))
          (upperUnipotent F (t + 1))).toReal : ℂ) *
        ∫ m in unipotentFundamentalDomain F (t + 1),
          dualFunction F (t + 1) (cuspFunction F T' v') ((m : Points F (t + 1)) * x) *
            (genericCharacter F t ψ (fun _ => 1) m)⁻¹ ∂Measure.haar := by
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  have hφ'm : Measurable (cuspFunction F T' v') := (continuous_cuspFunction F T' v').measurable
  have hW' := subgroupCharacterCoefficient_eq_setIntegral F (Scheme F (t + 1))
    (upperUnipotent F (t + 1)) (genericCharacter F t ψ⁻¹ fun _ => 1)
    (continuous_genericCharacter F t ψ⁻¹ hψ'.1 _).measurable
    (genericCharacter_rational_mul F t ψ⁻¹ hψ') (cuspFunction F T' v') hφ'm
    (fun k y => cuspFunction_rational_mul F T' v' (mem_rationalSubgroup_of_unipotent F k) y)
    (dualPoint F (t + 1) x)
  have hconj : ∀ n : unipotentAdelic F (t + 1),
      starRingEnd ℂ (genericCharacter F t ψ⁻¹ (fun _ => 1) n) =
        genericCharacter F t ψ (fun _ => 1) n := fun n => by
    rw [genericCharacter_inv F t ψ hψ.2.2.2, Complex.conj_conj]
  simp_rw [hconj] at hW'
  rw [dualFunction_eq]
  change cuspWhittaker F T' ψ⁻¹ v' (dualPoint F (t + 1) x) = _
  rw [show cuspWhittaker F T' ψ⁻¹ v' (dualPoint F (t + 1) x) = _ from hW', Complex.real_smul]
  congr 1
  have hG : ∀ (l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (t + 1))
      (upperUnipotent F (t + 1))) (m : unipotentAdelic F (t + 1)),
      cuspFunction F T' v' (((l : unipotentAdelic F (t + 1)) * m : unipotentAdelic F (t + 1)) *
          dualPoint F (t + 1) x) *
        genericCharacter F t ψ (fun _ => 1) ((l : unipotentAdelic F (t + 1)) * m) =
      cuspFunction F T' v' ((m : Points F (t + 1)) * dualPoint F (t + 1) x) *
        genericCharacter F t ψ (fun _ => 1) m := by
    intro l m
    rw [genericCharacter_rational_mul F t ψ hψ, Subgroup.coe_mul, mul_assoc,
      cuspFunction_rational_mul F T' v' (mem_rationalSubgroup_of_unipotent F l)]
  rw [← setIntegral_comp_dualConjUnipotent F (t + 1) hG]
  refine setIntegral_congr_fun
    (LeftCosetSpace.measurableSet_fundamentalDomain _ _) fun m _ => ?_
  simp only [dualFunction_eq]
  rw [dualPoint_mul, ← coe_dualConjUnipotent, genericCharacter_dualConjUnipotent]

end DualWhittaker

section DualKernels

variable (F : Type u) [Field F] [NumberField F]

/-- `(∫_x W(rect(g, x)) dx) Φ(g) |det g|^(s-(r-t)/2)`. -/
def dualKernel {r t : ℕ} (h : t < r) (W : Points F (r + 1) → ℂ) (Φ : Points F (t + 1) → ℂ)
    (s : ℂ) (g : Points F (t + 1)) : ℂ :=
  dualRectIntegral F h W g * Φ g * detPower F (t + 1) g (s - ((r - t : ℕ) : ℂ) / 2)

theorem dualWhittakerIntegrand_eq {r t : ℕ} (h : t < r) (W : Points F (r + 1) → ℂ)
    (W' : Points F (t + 1) → ℂ) (s : ℂ) (q : WhittakerQuotient F (t + 1)) :
    dualWhittakerIntegrand F h W W' s q = dualKernel F h W W' s q.out := by
  unfold dualWhittakerIntegrand dualWhittakerKernel dualKernel dualRectIntegral
  rw [integral_mul_const, integral_mul_const]

/-- The integrand of the dual defining integral, at a point of `GL_m(𝔸)`. -/
def dualProjectionKernel {r t : ℕ} (h : t < r) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (φ' : Points F (t + 1) → ℂ) (s : ℂ) (x : Points F (t + 1)) : ℂ :=
  dualProjection F (Nat.succ_lt_succ h) ψ φ (pad F (Nat.le_succ (t + 1)) x) * φ' x *
    detPower F (t + 1) x (s - 1 / 2)

theorem dualUnequalIntegral_eq {r t : ℕ} (h : t < r) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (φ' : Points F (t + 1) → ℂ) (s : ℂ) :
    dualUnequalIntegral F h ψ φ φ' s =
      ∫ q, dualProjectionKernel F h ψ φ φ' s q.out
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)) := rfl

theorem measurable_dualKernel {r t : ℕ} (h : t < r) {W : Points F (r + 1) → ℂ}
    {Φ : Points F (t + 1) → ℂ} (hW : Measurable W) (hΦ : Measurable Φ) (s : ℂ) :
    Measurable (dualKernel F h W Φ s) :=
  ((measurable_dualRectIntegral F h hW).mul hΦ).mul
    (continuous_detPower F (t + 1) _).measurable

variable [CompactSpace (AdeleQuotient F)]

/-- The dual Whittaker expansion of the dual projection: for `h ∈ GL_m(𝔸)` the rectangular
integrals converge absolutely and
`P̃φ̃(diag(h,1)) = |det h|^{-(n-m-1)/2} Σ_{γ ∈ N_m(F) \ GL_m(F)} ∫ W̃(rect(γh, x) w') dx`,
with `W̃` the dualized Whittaker function translated by `w' = diag(I_m, w_{n-m})`. -/
def DualProjectionWhittakerExpansion {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) : Prop :=
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (g : Points F (t + 1)),
      Integrable (fun x => dualWhittaker F h T ψ v (rectangularPoint F h g x))
          (rectangleMeasure F (r - (t + 1)) (t + 1)) ∧
        HasSum (fun q : RationalCosetIndex F (t + 1) =>
            detPower F (t + 1) g (-((r - (t + 1) : ℕ) : ℂ) / 2) *
              dualRectIntegral F h (dualWhittaker F h T ψ v) (rationalCosetRep F (t + 1) q * g))
          (dualProjection F (Nat.succ_lt_succ h) ψ (dualFunction F (r + 1) (cuspFunction F T v))
            (pad F (Nat.le_succ (t + 1)) g))

/-- Left translation of the dual kernel by `N_m(𝔸)`. -/
theorem dualKernel_unipotent_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (Φ : Points F (t + 1) → ℂ) (s : ℂ)
    (n : unipotentAdelic F (t + 1)) (x : Points F (t + 1)) :
    dualKernel F h (dualWhittaker F h T ψ v) Φ s ((n : Points F (t + 1)) * x) =
      (genericCharacter F t ψ (fun _ => 1) n)⁻¹ *
        (dualRectIntegral F h (dualWhittaker F h T ψ v) x * Φ ((n : Points F (t + 1)) * x) *
          detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2)) := by
  unfold dualKernel
  rw [dualRectIntegral_unipotent_mul F h T ψ hψ v, detPower_unipotent_mul]
  ring

/-- The dual kernel with the dual cusp form is left invariant under `N_m(F)`. -/
theorem dualKernel_rational_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    {k : Points F (t + 1)} (hk : k ∈ unipotentRationalImage F (t + 1)) (x : Points F (t + 1)) :
    dualKernel F h (dualWhittaker F h T ψ v) (dualFunction F (t + 1) (cuspFunction F T' v')) s
        (k * x) =
      dualKernel F h (dualWhittaker F h T ψ v) (dualFunction F (t + 1) (cuspFunction F T' v')) s
        x := by
  have hkΓ := unipotentRationalImage_le F (t + 1) hk
  obtain ⟨l, rfl⟩ := (mem_unipotentRationalImage_iff F (t + 1) k).mp hk
  rw [dualKernel_unipotent_mul F h T ψ hψ v, genericCharacter_rational F t ψ hψ.2.2.1, inv_one,
    one_mul, dualCuspFunction_rational_mul F T' v' hkΓ]
  rfl

/-- The dual Whittaker kernel is left invariant under `N_m(𝔸)`. -/
theorem dualKernel_whittaker_unipotent_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    (n : unipotentAdelic F (t + 1)) (x : Points F (t + 1)) :
    dualKernel F h (dualWhittaker F h T ψ v) (dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v'))
        s ((n : Points F (t + 1)) * x) =
      dualKernel F h (dualWhittaker F h T ψ v)
        (dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v')) s x := by
  rw [dualKernel_unipotent_mul F h T ψ hψ v, dualCuspWhittaker_unipotent_mul F T' ψ hψ v']
  have hne := genericCharacter_ne_zero F t ψ hψ (fun _ => 1) n
  unfold dualKernel
  field_simp

/-- The dual defining integrand is the orbit sum of the dual kernel. -/
theorem hasSum_dualProjectionKernel {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t)
    (hE : DualProjectionWhittakerExpansion F h T) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    (x : Points F (t + 1)) :
    HasSum (fun q => dualKernel F h (dualWhittaker F h T ψ v)
        (dualFunction F (t + 1) (cuspFunction F T' v')) s (rationalCosetRep F (t + 1) q * x))
      (dualProjectionKernel F h ψ (dualFunction F (r + 1) (cuspFunction F T v))
        (dualFunction F (t + 1) (cuspFunction F T' v')) s x) := by
  have h1 := (hE ψ hψ v x).2.mul_right
    (dualFunction F (t + 1) (cuspFunction F T' v') x * detPower F (t + 1) x (s - 1 / 2))
  convert h1 using 1
  · funext q
    have hq : rationalCosetRep F (t + 1) q ∈
        AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1)) := cosetRep_mem _ _ q
    unfold dualKernel
    rw [dualCuspFunction_rational_mul F T' v' hq, detPower_rational_mul F (t + 1) hq,
      ← detPower_unfolding_exponent F h x s]
    ring
  · unfold dualProjectionKernel
    ring

end DualKernels

section DualUnfolding

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Averaging the dual kernel of the dual cusp form over `N_m(F) \ N_m(𝔸)` gives the mass
times the dual kernel of the dual Whittaker function. -/
theorem setIntegral_unipotent_dualKernel {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    (x : Points F (t + 1)) :
    ∫ n in unipotentFundamentalDomain F (t + 1),
        dualKernel F h (dualWhittaker F h T ψ v) (dualFunction F (t + 1) (cuspFunction F T' v')) s
          ((n : Points F (t + 1)) * x) ∂Measure.haar =
      ((Measure.haar : Measure (unipotentAdelic F (t + 1)))
          (unipotentFundamentalDomain F (t + 1))).toReal •
        dualKernel F h (dualWhittaker F h T ψ v)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v')) s x := by
  set a : ℝ := ((Measure.haar : Measure (unipotentAdelic F (t + 1)))
    (unipotentFundamentalDomain F (t + 1))).toReal with ha
  set c : ℝ := (AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F (t + 1))
    (upperUnipotent F (t + 1))).toReal with hc
  have hac : (c : ℂ) * (a : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ha, hc, quotientMassNormalizer_mul_haar, Complex.ofReal_one]
  simp_rw [dualKernel_unipotent_mul F h T ψ hψ v (dualFunction F (t + 1) (cuspFunction F T' v')) s]
  have e1 : (fun n : unipotentAdelic F (t + 1) => (genericCharacter F t ψ (fun _ => 1) n)⁻¹ *
      (dualRectIntegral F h (dualWhittaker F h T ψ v) x *
        dualFunction F (t + 1) (cuspFunction F T' v') ((n : Points F (t + 1)) * x) *
          detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2))) =
      fun n : unipotentAdelic F (t + 1) =>
        (dualRectIntegral F h (dualWhittaker F h T ψ v) x *
          detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2)) *
        (dualFunction F (t + 1) (cuspFunction F T' v') ((n : Points F (t + 1)) * x) *
          (genericCharacter F t ψ (fun _ => 1) n)⁻¹) := by
    funext n
    ring
  rw [e1, integral_const_mul]
  unfold dualKernel
  rw [dualCuspWhittaker_eq_setIntegral F T' ψ hψ v' x, Complex.real_smul]
  linear_combination (-(dualRectIntegral F h (dualWhittaker F h T ψ v) x *
      detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2) *
      ∫ n in unipotentFundamentalDomain F (t + 1),
        dualFunction F (t + 1) (cuspFunction F T' v') ((n : Points F (t + 1)) * x) *
          (genericCharacter F t ψ (fun _ => 1) n)⁻¹ ∂Measure.haar)) * hac

/-- The dual Whittaker function is bounded by the mass normalizer times the integral of the
absolute value of the dual cusp form over the fundamental domain in `N_m(𝔸)`. -/
theorem norm_dualCuspWhittaker_le {t : ℕ}
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v' : T'.Space) (x : Points F (t + 1)) :
    ‖dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v') x‖ ≤
      (AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F (t + 1))
          (upperUnipotent F (t + 1))).toReal *
        ∫ m in unipotentFundamentalDomain F (t + 1),
          ‖dualFunction F (t + 1) (cuspFunction F T' v') ((m : Points F (t + 1)) * x)‖
            ∂Measure.haar := by
  rw [dualCuspWhittaker_eq_setIntegral F T' ψ hψ v' x, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ENNReal.toReal_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext m
  rw [norm_mul, norm_inv, norm_genericCharacter F t ψ hψ.2.2.2, inv_one, mul_one]

/-- Dual unfolding (Cogdell 2004, p.207), from the dual Whittaker expansion and absolute
integrability of the dual kernel over `N_m(F) \ GL_m(𝔸)`. -/
theorem dual_unfolding {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t)
    (hE : DualProjectionWhittakerExpansion F h T) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    (hint : Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (t + 1)) =>
        (∫ x, ‖dualWhittaker F h T ψ v (rectangularPoint F h q.out x)‖
          ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
        ‖dualFunction F (t + 1) (cuspFunction F T' v') q.out‖ *
        ‖detPower F (t + 1) q.out (s - ((r - t : ℕ) : ℂ) / 2)‖)
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1)))) :
    DualWhittakerAbsolutelyConvergent F h (dualWhittaker F h T ψ v)
        (dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v')) s ∧
      dualUnequalIntegral F h ψ (dualFunction F (r + 1) (cuspFunction F T v))
          (dualFunction F (t + 1) (cuspFunction F T' v')) s =
        dualWhittakerIntegral F h (dualWhittaker F h T ψ v)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v')) s := by
  -- abbreviations through local definitions
  let Wd := dualWhittaker F h T ψ v
  let φd := dualFunction F (t + 1) (cuspFunction F T' v')
  let Wd' := dualFunction F (t + 1) (cuspWhittaker F T' ψ⁻¹ v')
  let R : Points F (t + 1) → ℝ := fun g =>
    ∫ x, ‖Wd (rectangularPoint F h g x)‖ ∂rectangleMeasure F (r - (t + 1)) (t + 1)
  let Dn : Points F (t + 1) → ℝ := fun g => ‖detPower F (t + 1) g (s - ((r - t : ℕ) : ℂ) / 2)‖
  let f₃ : Points F (t + 1) → ℂ := fun g => ((R g * ‖φd g‖ * Dn g : ℝ) : ℂ)
  let g₃ : Points F (t + 1) → ℂ := fun g => ((R g * ‖Wd' g‖ * Dn g : ℝ) : ℂ)
  have hWdm : Measurable Wd := measurable_dualWhittaker F h T ψ hψ v
  have hRm : Measurable R := measurable_dualRectNormIntegral F h hWdm
  have hR0 : ∀ g, 0 ≤ R g := fun g => integral_nonneg fun x => norm_nonneg _
  have hDnm : Measurable Dn := (continuous_detPower F (t + 1) _).norm.measurable
  have hφdm : Measurable φd := (continuous_dualCuspFunction F T' v').measurable
  have hWd'm : Measurable Wd' := measurable_dualCuspWhittaker F T' ψ hψ v'
  have hf₃m : Measurable f₃ :=
    Complex.measurable_ofReal.comp ((hRm.mul hφdm.norm).mul hDnm)
  have hg₃m : Measurable g₃ :=
    Complex.measurable_ofReal.comp ((hRm.mul hWd'm.norm).mul hDnm)
  have hRN : ∀ (n : unipotentAdelic F (t + 1)) (g : Points F (t + 1)),
      R ((n : Points F (t + 1)) * g) = R g :=
    fun n g => dualRectNormIntegral_unipotent_mul F h T ψ hψ v n g
  have hDnN : ∀ (n : unipotentAdelic F (t + 1)) (g : Points F (t + 1)),
      Dn ((n : Points F (t + 1)) * g) = Dn g := fun n g => by
    simp only [Dn, detPower_unipotent_mul]
  -- invariances
  have hf₃Λ : ∀ k ∈ unipotentRationalImage F (t + 1), ∀ g : Points F (t + 1),
      f₃ (k * g) = f₃ g := by
    intro k hk g
    have hkΓ := unipotentRationalImage_le F (t + 1) hk
    obtain ⟨l, rfl⟩ := (mem_unipotentRationalImage_iff F (t + 1) k).mp hk
    simp only [f₃, hRN, hDnN, φd, dualCuspFunction_rational_mul F T' v' hkΓ]
  have hg₃N : ∀ (n : unipotentAdelic F (t + 1)) (g : Points F (t + 1)),
      g₃ ((n : Points F (t + 1)) * g) = g₃ g := by
    intro n g
    simp only [g₃, hRN, hDnN, Wd', dualCuspWhittaker_unipotent_mul F T' ψ hψ v', norm_mul,
      norm_genericCharacter F t ψ hψ.2.2.2, one_mul]
  have hf₀m : Measurable (dualKernel F h Wd φd s) := measurable_dualKernel F h hWdm hφdm s
  have hf₂m : Measurable (dualKernel F h Wd Wd' s) := measurable_dualKernel F h hWdm hWd'm s
  have hf₀Λ : ∀ k ∈ unipotentRationalImage F (t + 1), ∀ x : Points F (t + 1),
      dualKernel F h Wd φd s (k * x) = dualKernel F h Wd φd s x :=
    fun k hk x => dualKernel_rational_mul F h T T' ψ hψ v v' s hk x
  -- integrability of the gauge function and of the kernel on the fundamental domain
  have hf₃sΛ : IntegrableOn f₃ (LeftCosetSpace.fundamentalDomain
      (unipotentRationalImage F (t + 1)) (isDiscrete_unipotentRationalImage F (t + 1)))
      Measure.haar :=
    (integrable_out_iff _ hf₃m (fun k x => hf₃Λ k k.property x) _ _).mp hint.ofReal
  have hnormA : ∀ g, ‖dualRectIntegral F h Wd g‖ ≤ R g := fun g =>
    norm_integral_le_integral_norm _
  have hf₀sΛ : IntegrableOn (dualKernel F h Wd φd s) (LeftCosetSpace.fundamentalDomain
      (unipotentRationalImage F (t + 1)) (isDiscrete_unipotentRationalImage F (t + 1)))
      Measure.haar := by
    refine hf₃sΛ.norm.mono' hf₀m.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have e3 : ‖f₃ g‖ = R g * ‖φd g‖ * Dn g := by
      simp only [f₃, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg (mul_nonneg (hR0 g) (norm_nonneg _)) (norm_nonneg _))
    rw [e3]
    unfold dualKernel
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hnormA g) (norm_nonneg _))
      (norm_nonneg _)
  -- averaging and the Whittaker side
  obtain ⟨hf₂sΛ, havg⟩ := setIntegral_eq_of_average F hf₀m hf₀Λ hf₀sΛ
    (setIntegral_unipotent_dualKernel F h T T' ψ hψ v v' s)
  obtain ⟨hint₂, hR⟩ := integrable_and_integral_whittakerQuotient F hf₂m
    (dualKernel_whittaker_unipotent_mul F h T T' ψ hψ v v' s) hf₂sΛ
  -- the absolute values
  have hg₃sΛ : IntegrableOn g₃ (LeftCosetSpace.fundamentalDomain
      (unipotentRationalImage F (t + 1)) (isDiscrete_unipotentRationalImage F (t + 1)))
      Measure.haar := by
    obtain ⟨havint, -⟩ := integrableOn_and_setIntegral_average F hf₃m hf₃Λ hf₃sΛ
    refine (havint.norm.const_mul (AdelicSubgroupPoints.quotientMassNormalizer F
      (Scheme F (t + 1)) (upperUnipotent F (t + 1))).toReal).mono' hg₃m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    have hav : ∫ n in unipotentFundamentalDomain F (t + 1),
        f₃ ((n : Points F (t + 1)) * g) ∂Measure.haar =
        (((R g * Dn g) * ∫ n in unipotentFundamentalDomain F (t + 1),
          ‖φd ((n : Points F (t + 1)) * g)‖ ∂Measure.haar : ℝ) : ℂ) := by
      simp only [f₃, hRN, hDnN]
      rw [integral_complex_ofReal]
      congr 1
      rw [← integral_const_mul]
      congr 1
      funext n
      ring
    have e3 : ‖g₃ g‖ = R g * ‖Wd' g‖ * Dn g := by
      simp only [g₃, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg (mul_nonneg (hR0 g) (norm_nonneg _)) (norm_nonneg _))
    have e4 : ‖∫ n in unipotentFundamentalDomain F (t + 1),
        f₃ ((n : Points F (t + 1)) * g) ∂Measure.haar‖ =
        R g * Dn g * ∫ n in unipotentFundamentalDomain F (t + 1),
          ‖φd ((n : Points F (t + 1)) * g)‖ ∂Measure.haar := by
      rw [hav, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg (mul_nonneg (hR0 g) (norm_nonneg _))
        (integral_nonneg fun n => norm_nonneg _))
    rw [e3, e4]
    have hb := norm_dualCuspWhittaker_le F T' ψ hψ v' g
    calc R g * ‖Wd' g‖ * Dn g ≤ R g * ((AdelicSubgroupPoints.quotientMassNormalizer F
          (Scheme F (t + 1)) (upperUnipotent F (t + 1))).toReal *
          ∫ n in unipotentFundamentalDomain F (t + 1),
            ‖φd ((n : Points F (t + 1)) * g)‖ ∂Measure.haar) * Dn g := by
          gcongr
      _ = _ := by ring
  obtain ⟨hint₃, -⟩ := integrable_and_integral_whittakerQuotient F hg₃m hg₃N hg₃sΛ
  refine ⟨⟨Filter.Eventually.of_forall fun q => ?_, ?_, ?_⟩, ?_⟩
  · exact ((hE ψ hψ v q.out).1.mul_const _).mul_const _
  · have heq : (fun q : WhittakerQuotient F (t + 1) =>
        ∫ x, ‖dualWhittakerKernel F h Wd Wd' s q x‖ ∂rectangleMeasure F (r - (t + 1)) (t + 1)) =
        fun q => (g₃ q.out).re := by
      funext q
      simp only [g₃, Complex.ofReal_re, dualWhittakerKernel, norm_mul]
      rw [integral_mul_const, integral_mul_const]
    rw [heq]
    exact hint₃.re
  · have heq : dualWhittakerIntegrand F h Wd Wd' s = fun q => dualKernel F h Wd Wd' s q.out :=
      funext fun q => dualWhittakerIntegrand_eq F h Wd Wd' s q
    rw [heq]
    exact hint₂
  · have heq : dualWhittakerIntegrand F h Wd Wd' s = fun q => dualKernel F h Wd Wd' s q.out :=
      funext fun q => dualWhittakerIntegrand_eq F h Wd Wd' s q
    rw [dualUnequalIntegral_eq, integral_rationalQuotient_eq_of_hasSum F hf₀m hf₀Λ
      (hasSum_dualProjectionKernel F h T T' hE ψ hψ v v' s) hf₀sΛ, havg, ← hR,
      dualWhittakerIntegral, heq]

end DualUnfolding

end Langlands.Global.RankinSelbergGlobal.Unfolding
