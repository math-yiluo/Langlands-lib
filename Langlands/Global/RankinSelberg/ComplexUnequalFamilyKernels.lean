import Langlands.Global.RankinSelberg.ComplexLocalUnequalKernels
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints

/-! # Continuity of the exact unequal-rank kernels for continuous Whittaker families -/

noncomputable section
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.QuotientIntegration
open scoped Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalFamily

open ArchimedeanLocal

section Equivariance

variable {r t : ℕ}
local notation "GL[" n "]" => Langlands.GeneralLinear (n + 1) ℂ
local notation "Unip[" n "]" => GeneralLinear.upperUnipotent (n + 1) ℂ

/-- Left covariance with the given complex trace character. -/
def HasLeftCharacter (a : ℂˣ) (W : GL[r] → ℂ) : Prop :=
  ∀ (u : Unip[r]) (g : GL[r]), W (u.val * g) = complexWhittakerCharacter a u.val * W g

private theorem padGL_mem_upperUnipotent (h : t < r) (u : Unip[t]) :
    padGL (Nat.succ_le_succ h.le) u.val ∈ Unip[r] := by
  constructor
  · intro i j hij
    change j < i at hij
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_eq_zero u hij
    · exact Matrix.one_apply_ne hij.ne'
  · intro i
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_diag u _
    · exact Matrix.one_apply_eq i

private theorem complexWhittakerCharacter_padGL (a : ℂˣ) (h : t < r) (u : Unip[t]) :
    complexWhittakerCharacter a (padGL (Nat.succ_le_succ h.le) u.val) =
      complexWhittakerCharacter a u.val := by
  apply congrArg (fun z : ℂ => (complexScaledCharacter a).complex z)
  let e := Fin.castLEEmb h.le
  calc
    _ = ∑ i ∈ Finset.univ.map e, (padGL (Nat.succ_le_succ h.le) u.val :
        Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) i.castSucc i.succ := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have ht : ¬ i.val < t := by
        intro ht
        exact hi (Finset.mem_map.mpr ⟨⟨i.val, ht⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      rw [UnequalAnalytic.padGL_apply, dite_eq_right (fun h' => ht (Nat.lt_of_succ_lt_succ h'.2))]
      exact Matrix.one_apply_ne (ne_of_lt i.castSucc_lt_succ)
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      rw [UnequalAnalytic.padGL_apply]
      have hi : (e i).castSucc.val < t + 1 ∧ (e i).succ.val < t + 1 :=
        ⟨Nat.lt_succ_of_lt i.isLt, Nat.succ_lt_succ i.isLt⟩
      rw [dite_eq_left hi]
      rfl

private theorem complexWhittakerCharacter_neg (a : ℂˣ) (u : GL[r]) :
    complexWhittakerCharacter (-a) u =
      (complexScaledCharacter a).complex
        (-(∑ i : Fin r, u.val i.castSucc i.succ)) := by
  simp only [complexWhittakerCharacter, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    complexScaledCharacter_apply, Units.val_neg, neg_mul, mul_neg]

private theorem complexWhittakerCharacter_mul_neg (a : ℂˣ) (u : GL[r]) :
    complexWhittakerCharacter a u * complexWhittakerCharacter (-a) u = 1 := by
  rw [complexWhittakerCharacter_neg, complexWhittakerCharacter, ← AddChar.map_add_eq_mul,
    add_neg_cancel, AddChar.map_zero_eq_one]

private theorem complexWhittakerCharacter_reflected (a : ℂˣ) (u : Unip[r]) :
    complexWhittakerCharacter a (Whittaker.reflectedUnipotent u).val =
      complexWhittakerCharacter (-a) u.val := by
  rw [complexWhittakerCharacter_neg]
  exact congrArg (fun z : ℂ => (complexScaledCharacter a).complex z)
    (Whittaker.reflectedUnipotent_sum u)

/-- Weyl inverse transpose changes the left character from `a` to `-a`. -/
theorem dual_left_mul {a : ℂˣ}
    {W : GL[r] → ℂ} (hW : HasLeftCharacter a W) (u : Unip[r]) (g : GL[r]) :
    ArchimedeanLocal.dualFunction (r + 1) W (u.val * g) =
      complexWhittakerCharacter (-a) u.val * ArchimedeanLocal.dualFunction (r + 1) W g := by
  change W (weylInverseTranspose (r + 1) ℂ (u.val * g)) =
    complexWhittakerCharacter (-a) u.val * W (weylInverseTranspose (r + 1) ℂ g)
  rw [Whittaker.weylInverseTranspose_left_unipotent,
    hW (Whittaker.reflectedUnipotent u),
    complexWhittakerCharacter_reflected]

end Equivariance

section Quotient

variable {r t : ℕ} (h : t < r)
local notation "GL[" n "]" => Langlands.GeneralLinear (n + 1) ℂ
local notation "Unip[" n "]" => GeneralLinear.upperUnipotent (n + 1) ℂ
local notation "Rect" => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ

private theorem archimedeanDetPower_unipotent_mul (u : Unip[t]) (g : GL[t]) (s : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs (u.val * g) s =
      ArchimedeanLocal.detPower complexNormalizedAbs g s := by
  simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul, RankinSelberg.unipotent_det,
    one_mul]

variable {a : ℂˣ}
variable {W : GL[r] → ℂ} {W' : GL[t] → ℂ}

private theorem complexUnequalProduct_unipotent_mul
    (hW : HasLeftCharacter a W) (hW' : HasLeftCharacter (-a) W')
    (u : Unip[t]) (g : GL[t]) :
    W (padGL (Nat.succ_le_succ h.le) (u.val * g)) * W' (u.val * g) =
      W (padGL (Nat.succ_le_succ h.le) g) * W' g := by
  rw [map_mul, hW ⟨padGL (Nat.succ_le_succ h.le) u.val, padGL_mem_upperUnipotent h u⟩,
    hW' u, complexWhittakerCharacter_padGL a h u,
    mul_mul_mul_comm, complexWhittakerCharacter_mul_neg, one_mul]

private theorem complexUnequalDualProduct_unipotent_mul
    (hW : HasLeftCharacter a W) (hW' : HasLeftCharacter (-a) W')
    (u : Unip[t]) (g : GL[t]) (x : Rect) :
    ArchimedeanLocal.dualFunction (r + 1) W
        (ArchimedeanLocal.rectangularPoint h (u.val * g) x * ArchimedeanLocal.unfoldingWeyl h) *
      ArchimedeanLocal.dualFunction (t + 1) W' (u.val * g) =
    ArchimedeanLocal.dualFunction (r + 1) W
        (ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h) *
      ArchimedeanLocal.dualFunction (t + 1) W' g := by
  let U : Unip[r] := ⟨padGL (Nat.succ_le_succ h.le) u.val, padGL_mem_upperUnipotent h u⟩
  rw [complexRectangularPoint_mul_left h, mul_assoc]
  change ArchimedeanLocal.dualFunction (r + 1) W
        (U.val * (ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h)) *
      ArchimedeanLocal.dualFunction (t + 1) W' (u.val * g) = _
  rw [dual_left_mul hW U, dual_left_mul hW' u]
  simp only [U, complexWhittakerCharacter_padGL (-a) h u, neg_neg]
  rw [mul_mul_mul_comm, mul_comm (complexWhittakerCharacter (-a) u.val),
    complexWhittakerCharacter_mul_neg, one_mul]

private theorem invariant_apply_out_mk {A : Type*} (f : GL[t] → A)
    (hf : ∀ u : Unip[t], ∀ g, f (u.val * g) = f g) (g : GL[t]) :
    f (Quotient.mk (QuotientGroup.rightRel (Unip[t])) g).out = f g :=
  congrArg (descend (Unip[t]) f hf) (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel (Unip[t])) g))

/-- The exact original kernel, evaluated at the class of any representative. -/
theorem ordinaryKernel_mk
    (hW : HasLeftCharacter a W) (hW' : HasLeftCharacter (-a) W')
    (s : ℂ) (g : GL[t]) :
    complexUnequalIntegrand h W W' s (Quotient.mk _ g) =
      W (padGL (Nat.succ_le_succ h.le) g) * W' g *
        ArchimedeanLocal.detPower complexNormalizedAbs g (s - ((r - t : ℕ) : ℂ) / 2) := by
  refine invariant_apply_out_mk (fun g => W (padGL (Nat.succ_le_succ h.le) g) * W' g *
    ArchimedeanLocal.detPower complexNormalizedAbs g (s - ((r - t : ℕ) : ℂ) / 2)) ?_ g
  intro u g
  rw [complexUnequalProduct_unipotent_mul h hW hW', archimedeanDetPower_unipotent_mul]

/-- The exact dual kernel evaluated using any representative, with the rectangle fixed. -/
theorem dualKernel_mk
    (hW : HasLeftCharacter a W) (hW' : HasLeftCharacter (-a) W')
    (s : ℂ) (g : GL[t]) (x : Rect) :
    complexUnequalDualKernel h W W' s (Quotient.mk _ g, x) =
      ArchimedeanLocal.dualFunction (r + 1) W
          (ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h) *
        ArchimedeanLocal.dualFunction (t + 1) W' g *
        ArchimedeanLocal.detPower complexNormalizedAbs g (s - ((r - t : ℕ) : ℂ) / 2) := by
  refine invariant_apply_out_mk (fun g =>
    ArchimedeanLocal.dualFunction (r + 1) W
        (ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h) *
      ArchimedeanLocal.dualFunction (t + 1) W' g *
      ArchimedeanLocal.detPower complexNormalizedAbs g (s - ((r - t : ℕ) : ℂ) / 2)) ?_ g
  intro u g
  rw [complexUnequalDualProduct_unipotent_mul h hW hW', archimedeanDetPower_unipotent_mul]

private theorem continuous_complexRectangularPoint :
    Continuous (fun p : GL[t] × Rect => ArchimedeanLocal.rectangularPoint h p.1 p.2) := by
  let e := finCongr (congrArg (fun n : ℕ => n + 1) (Nat.add_sub_of_le (Nat.succ_le_of_lt h)))
  have hpar : Continuous (fun p : GL[t] × Rect =>
      (p.1, p.2, (1 : GeneralLinear.lowerTriangularSubgroup (r - (t + 1)) ℂ))) :=
    continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have hblock := (GeneralLinear.continuous_lowerBlockLocalization
    (R := ℂ) (a := t + 1) (d := r - (t + 1)) 1).comp hpar
  exact (GeneralLinear.reindexContinuous (R := ℂ) e).continuous.comp hblock

private theorem continuous_archimedeanDetPower (s : ℂ) :
    Continuous (fun g : GL[t] => ArchimedeanLocal.detPower complexNormalizedAbs g s) := by
  have hdet : Continuous (fun g : GL[t] => Matrix.det g.val) := continuous_id.matrix_det.comp
    Units.continuous_val
  have habs : Continuous (fun g : GL[t] => complexNormalizedAbs (Matrix.det g.val)) :=
    hdet.norm.pow 2
  have hlog := habs.log (fun g =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero))
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

private theorem continuous_archimedeanDualFunction {n : ℕ}
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : Continuous f) :
    Continuous (ArchimedeanLocal.dualFunction n f) :=
  hf.comp (continuous_const.mul (GeneralLinear.continuous_inverseTranspose n ℂ))

/-- The original unequal-rank kernel is continuous on the actual left quotient. -/
theorem continuous_ordinaryKernel
    (hW : HasLeftCharacter a W) (hW' : HasLeftCharacter (-a) W')
    (hWc : Continuous W) (hWc' : Continuous W')
    (s : ℂ) : Continuous (complexUnequalIntegrand h W W' s) := by
  apply (leftQuotient_isOpenQuotientMap (Unip[t])).isQuotientMap.continuous_iff.mpr
  simp only [Function.comp_def, leftQuotientMap_apply, ordinaryKernel_mk h hW hW']
  exact ((hWc.comp (UnequalAnalytic.continuous_padGL (Nat.succ_le_succ h.le))).mul
    hWc').mul
      (continuous_archimedeanDetPower _)

/-- The dual unequal-rank kernel is jointly continuous on the left quotient and rectangle. -/
theorem continuous_dualKernel
    (hW : HasLeftCharacter a W) (hW' : HasLeftCharacter (-a) W')
    (hWc : Continuous W) (hWc' : Continuous W')
    (s : ℂ) : Continuous (complexUnequalDualKernel h W W' s) := by
  have hq := (leftQuotient_isOpenQuotientMap (Unip[t])).prodMap
    (IsOpenQuotientMap.id (X := Rect))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun p : GL[t] × Rect =>
    complexUnequalDualKernel h W W' s (Quotient.mk _ p.1, p.2))
  simp only [dualKernel_mk h hW hW']
  exact (((continuous_archimedeanDualFunction
    hWc).comp
      ((continuous_complexRectangularPoint h).mul continuous_const)).mul
    ((continuous_archimedeanDualFunction
      hWc').comp continuous_fst)).mul
    ((continuous_archimedeanDetPower _).comp continuous_fst)

end Quotient

/-- The exact ordinary and dual unequal-rank kernels are continuous for continuous functions
with the two opposite left Whittaker laws. -/
def ComplexUnequalFamilyKernelsStatement : Prop :=
  ∀ {r t : ℕ} (h : t < r) (a : ℂˣ) (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ),
    HasLeftCharacter a W → HasLeftCharacter (-a) V → Continuous W → Continuous V →
    ∀ s : ℂ, Continuous (complexUnequalIntegrand h W V s) ∧ Continuous (complexUnequalDualKernel h W V s)

theorem complexUnequalFamilyKernels : ComplexUnequalFamilyKernelsStatement := by
  intro r t h a W V hW hV hWc hVc s
  exact ⟨continuous_ordinaryKernel h hW hV hWc hVc s, continuous_dualKernel h hW hV hWc hVc s⟩

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalFamily
