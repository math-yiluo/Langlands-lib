import Langlands.Global.RankinSelberg.DualExpansionUnfold
import Langlands.Global.RankinSelberg.UnfoldingDual
import Langlands.Global.RankinSelberg.DualWhittakerExpansionStatement
import Langlands.Global.RankinSelberg.RectangleModulusStatement
import Langlands.Group.GL.LowerTriangularBlockCoordinates

/-! # The dual expansion `E'` from `J` and the dual Whittaker expansion -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F]

local instance dualFinalSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualFinalSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Geometry

variable {t k : ℕ}

/-- The Library's Weyl element `diag(I_m, w_(n-m))` is `wPoint`. -/
theorem unfoldingWeyl_eq_wPoint (h : t < t + 1 + k) :
    unfoldingWeyl F h = wPoint (F := F) (m := t + 1) (K := k) := by
  apply point_ext
  rw [pointMatrix_wPoint]
  ext a b
  simp only [pointMatrix, unfoldingWeyl, MulEquiv.apply_symm_apply]
  set e := finCongr (Nat.add_sub_of_le (Nat.le_of_lt (Nat.succ_lt_succ h)))
  obtain ⟨a', rfl⟩ := e.surjective a
  obtain ⟨b', rfl⟩ := e.surjective b
  simp only [GeneralLinear.reindex, MulEquiv.coe_mk, Units.coe_mapEquiv]
  change Matrix.reindex e e _ (e a') (e b') = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp only [wMat, e, finCongr_apply, Fin.ext_iff, wPerm_val, Fin.val_cast]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a' <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b' <;>
    simp only [GeneralLinear.blockSum_apply_left, GeneralLinear.blockSum_apply_right,
      GeneralLinear.blockSum_apply_left_right, GeneralLinear.blockSum_apply_right_left,
      GeneralLinear.weylLong_entry, Matrix.one_apply, Fin.ext_iff, Fin.val_castAdd,
      Fin.val_natAdd, Fin.val_rev, Units.val_one] <;>
    (have := i.isLt; have := j.isLt; split_ifs <;> first | rfl | (exfalso; omega))

theorem wPoint_mul_pad {m K : ℕ} (g : Points F m) :
    wPoint (F := F) (m := m) (K := K) * pad F (show m ≤ m + K + 1 by omega) g =
      pad F (show m ≤ m + K + 1 by omega) g * wPoint := by
  have key : wPoint (F := F) (m := m) (K := K) * pad F (show m ≤ m + K + 1 by omega) g * wPoint =
      pad F (show m ≤ m + K + 1 by omega) g := by
    apply point_ext
    ext a b
    rw [pointMatrix_wPoint_conj]
    simp only [pointMatrix, adelicEquiv_pad, padGL_apply]
    by_cases ha : (a : ℕ) < m
    · have hwa : wPerm a = a := by unfold wPerm; rw [dite_eq_left ha]
      rw [hwa]
      by_cases hb : (b : ℕ) < m
      · have hwb : wPerm b = b := by unfold wPerm; rw [dite_eq_left hb]
        rw [hwb]
      · have hwb : ¬ ((wPerm b : Fin (m + K + 1)) : ℕ) < m := by rw [wPerm_val, ite_eq_right hb]; omega
        rw [dite_eq_left ha, dite_eq_left ha, dite_eq_right hwb, dite_eq_right hb]
    · have hwa : ¬ ((wPerm a : Fin (m + K + 1)) : ℕ) < m := by rw [wPerm_val, ite_eq_right ha]; omega
      rw [dite_eq_right hwa, dite_eq_right ha]
      simp only [wPerm_eq_iff]
  calc wPoint (F := F) (m := m) (K := K) * pad F (show m ≤ m + K + 1 by omega) g
      = wPoint * pad F (show m ≤ m + K + 1 by omega) g * (wPoint * wPoint) := by
        rw [wPoint_mul_wPoint, mul_one]
    _ = (wPoint * pad F (show m ≤ m + K + 1 by omega) g * wPoint) * wPoint := by
        simp only [mul_assoc]
    _ = pad F (show m ≤ m + K + 1 by omega) g * wPoint := by rw [key]

theorem rectangularPoint_one (h : t < t + 1 + k)
    (x : Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    rectangularPoint F h 1 x =
      xcPoint F (m := t + 1) (K := k) (fun q => x (Fin.cast (by omega) q.1) q.2) 0 := by
  apply point_ext
  rw [pointMatrix_xcPoint]
  ext a b
  simp only [pointMatrix, rectangularPoint, MulEquiv.apply_symm_apply, map_one]
  set e := finCongr (congrArg (fun a : ℕ => a + 1) (Nat.add_sub_of_le (Nat.succ_le_of_lt h)))
  obtain ⟨a', rfl⟩ := e.surjective a
  obtain ⟨b', rfl⟩ := e.surjective b
  simp only [GeneralLinear.reindex, MulEquiv.coe_mk, Units.coe_mapEquiv]
  change Matrix.reindex e e _ (e a') (e b') = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp only [e, finCongr_apply, Matrix.add_apply, Matrix.one_apply, xcMat, Fin.ext_iff,
    Fin.val_cast, Pi.zero_apply]
  refine Fin.addCases (fun a₁ => ?_) (fun a₃ => ?_) a' <;>
    refine Fin.addCases (fun b₁ => ?_) (fun b₃ => ?_) b'
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) a₁ <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) b₁ <;>
      simp only [GeneralLinear.lowerBlockLocalization, GeneralLinear.rankInclusion,
        MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply,
        GeneralLinear.blockSum_apply_left, GeneralLinear.lowerBlockPair_11,
        GeneralLinear.lowerBlockPair_12, GeneralLinear.lowerBlockPair_21,
        GeneralLinear.lowerBlockPair_22, Fin.val_castAdd, Fin.val_natAdd, Units.val_one,
        Matrix.one_apply, Fin.ext_iff, OneMemClass.coe_one] <;>
      (have := i.isLt; have := j.isLt; split_ifs <;>
        first
          | (simp; done)
          | (exfalso; omega))
  · have := a₁.isLt
    have := b₃.isLt
    simp only [GeneralLinear.lowerBlockLocalization, GeneralLinear.rankInclusion,
      MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply,
      GeneralLinear.blockSum_apply_left_right, Fin.val_castAdd, Fin.val_natAdd]
    split_ifs <;> first | (simp; done) | (exfalso; omega)
  · have := a₃.isLt
    have := b₁.isLt
    simp only [GeneralLinear.lowerBlockLocalization, GeneralLinear.rankInclusion,
      MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply,
      GeneralLinear.blockSum_apply_right_left, Fin.val_castAdd, Fin.val_natAdd]
    split_ifs <;> first | (simp; done) | (exfalso; omega)
  · have := a₃.isLt
    have := b₃.isLt
    simp only [GeneralLinear.lowerBlockLocalization, GeneralLinear.rankInclusion,
      MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply,
      GeneralLinear.blockSum_apply_right, Fin.val_natAdd, Units.val_one,
      Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | (simp; done) | (exfalso; omega)

theorem rankInclusion_eq_lowerBlockPair {R : Type*} [CommRing R] {a d : ℕ}
    (G : Langlands.GeneralLinear a R) :
    GeneralLinear.rankInclusion d G = GeneralLinear.lowerBlockPair G 0 1 := by
  ext i j
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;>
    simp [GeneralLinear.rankInclusion, Matrix.one_apply]

/-- `rect(1, x) diag(g, I) = rect(g, x g)`. -/
theorem rectangularPoint_one_mul_pad {r : ℕ} (h : t < r)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) (g : Points F (t + 1)) :
    rectangularPoint F h 1 x * pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g =
      rectangularPoint F h g (x * ((GeneralLinearGroupPoints.adelicEquiv F (t + 1) g :
        Matrix.GeneralLinearGroup (Fin (t + 1)) (Adeles F)) :
          Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F))) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [map_mul, adelicEquiv_pad]
  simp only [rectangularPoint, MulEquiv.apply_symm_apply, map_one]
  rw [← reindex_rankInclusion_rankInclusion (d := r - (t + 1)) (by omega)
      (Nat.le_of_lt (Nat.succ_lt_succ h)), ← map_mul,
    GeneralLinear.lowerBlockLocalization, GeneralLinear.lowerBlockLocalization, ← map_mul,
    rankInclusion_eq_lowerBlockPair (d := r - (t + 1))
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g),
    GeneralLinear.lowerBlockPair_mul_lowerBlockPair]
  simp

/-- `diag(g, I) = rect(g, 0)`. -/
theorem pad_eq_rectangularPoint {r : ℕ} (h : t < r) (g : Points F (t + 1)) :
    pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g = rectangularPoint F h g 0 := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [adelicEquiv_pad]
  simp only [rectangularPoint, MulEquiv.apply_symm_apply]
  rw [← reindex_rankInclusion_rankInclusion (d := r - (t + 1)) (by omega)
      (Nat.le_of_lt (Nat.succ_lt_succ h)),
    GeneralLinear.lowerBlockLocalization, rankInclusion_eq_lowerBlockPair (d := r - (t + 1))
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g)]

end Geometry

section DualWhittaker

variable [CompactSpace (AdeleQuotient F)]

local instance dualFinalQuotientBorel (r : ℕ) :
    BorelSpace (AdelicSubgroupPoints.RationalQuotient F (Scheme F (r + 1))
      (upperUnipotent F (r + 1))) :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F _ _

/-- Cusp Whittaker functions are continuous. -/
theorem continuous_cuspWhittaker' {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) :
    Continuous (cuspWhittaker F T ψ v) := by
  have hcpt := compactSpace_unipotentRationalQuotient F (r + 1)
  have hprob := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F
    (Scheme F (r + 1)) (upperUnipotent F (r + 1))
  set Γ := AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
  have hφ : ∀ (g : Points F (r + 1)) (g₀ : Γ) (n : unipotentAdelic F (r + 1)),
      cuspFunction F T v ((((g₀ : unipotentAdelic F (r + 1)) * n : unipotentAdelic F (r + 1)) :
          Points F (r + 1)) * g) *
        starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) ((g₀ : unipotentAdelic F (r + 1)) * n)) =
      cuspFunction F T v ((n : Points F (r + 1)) * g) *
        starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n) := by
    intro g g₀ n
    rw [Subgroup.coe_mul, mul_assoc,
      cuspFunction_rational_mul F T v (mem_rationalSubgroup_of_unipotent F g₀),
      genericCharacter_rational_mul F r ψ hψ]
  have hint : ∀ (g : Points F (r + 1))
      (x : AdelicSubgroupPoints.RationalQuotient F (Scheme F (r + 1)) (upperUnipotent F (r + 1))),
      cuspFunction F T v (((Quotient.out x : unipotentAdelic F (r + 1)) : Points F (r + 1)) * g) *
          starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) (Quotient.out x)) =
        LeftCosetSpace.lift Γ (fun n : unipotentAdelic F (r + 1) =>
          cuspFunction F T v ((n : Points F (r + 1)) * g) *
            starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n)) (hφ g) x := by
    intro g x
    conv_rhs => rw [← Quotient.out_eq x]
    rfl
  unfold cuspWhittaker generalLinearWhittakerFunction subgroupCharacterCoefficient
  simp_rw [hint]
  refine Langlands.Automorphic.CuspidalWhittaker.continuous_integral_of_continuous_uncurry _ ?_
  have hq : IsOpenQuotientMap (Prod.map (id : Points F (r + 1) → Points F (r + 1))
      (LeftCosetSpace.mk Γ)) :=
    IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)
  rw [hq.isQuotientMap.continuous_iff]
  have hc : Continuous fun p : Points F (r + 1) × unipotentAdelic F (r + 1) =>
      cuspFunction F T v ((p.2 : Points F (r + 1)) * p.1) *
        starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) p.2) :=
    ((continuous_cuspFunction F T v).comp
      ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)).mul
      (Complex.continuous_conj.comp
        ((continuous_genericCharacter F r ψ hψ.1 _).comp continuous_snd))
  exact hc.congr fun p => rfl

/-- The dual Whittaker function of a cusp form with a dual Whittaker expansion is a dual
Whittaker-type function. -/
theorem dualData_dualCuspWhittaker {m K : ℕ} (T : Automorphic.CuspidalOperatorRealization F (m + K))
    (hT : DualCuspidalWhittakerExpansion F T) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) :
    DualData F m ψ K (dualFunction F (m + K + 1) (cuspWhittaker F T ψ v)) where
  continuous := (continuous_cuspWhittaker' T ψ hψ v).comp (continuous_dualPoint F _)
  equivariant n g := by
    have := dualCuspWhittaker_unipotent_mul F T ψ⁻¹ (isStandardAdditiveCharacter_inv F ψ hψ) v n g
    rw [inv_inv] at this
    rw [this, genericCharacter_inv_eq_inv]
  summable := by
    obtain ⟨h1, h2⟩ := hT ψ hψ v
    refine ⟨fun g => ?_, fun C hC => ?_⟩
    · simp only [cornerFamily, padRational_eq_cornerAdelicPoint]
      exact (h1 g).1
    · simp only [cornerFamily, padRational_eq_cornerAdelicPoint]
      exact h2 C hC

theorem cornerSum_dualCuspWhittaker {m K : ℕ}
    (T : Automorphic.CuspidalOperatorRealization F (m + K))
    (hT : DualCuspidalWhittakerExpansion F T) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (g : Points F (m + K + 1)) :
    cornerSum F m K (dualFunction F (m + K + 1) (cuspWhittaker F T ψ v)) g =
      dualFunction F (m + K + 1) (cuspFunction F T v) g := by
  unfold cornerSum cornerFamily
  simp only [padRational_eq_cornerAdelicPoint]
  exact ((hT ψ hψ v).1 g).2.tsum_eq

end DualWhittaker

section Measure

local instance dualFinalRectMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _
local instance dualFinalRectBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

theorem integral_rect_cast {K₁ K₂ m : ℕ} (e : K₁ = K₂)
    (f : Matrix (Fin K₁) (Fin m) (Adeles F) → ℂ) :
    ∫ x, f x ∂rectangleMeasure F K₁ m =
      ∫ v, f (Matrix.of fun i j => v (Fin.cast e i) j) ∂rectangleMeasure F K₂ m := by
  subst e
  rfl

theorem integrable_rect_cast {K₁ K₂ m : ℕ} (e : K₁ = K₂)
    (f : Matrix (Fin K₁) (Fin m) (Adeles F) → ℂ) :
    Integrable f (rectangleMeasure F K₁ m) ↔
      Integrable (fun v => f (Matrix.of fun i j => v (Fin.cast e i) j))
        (rectangleMeasure F K₂ m) := by
  subst e
  rfl

variable [CompactSpace (AdeleQuotient F)]

/-- **Right translation of rectangle integrals** (from `J`). -/
theorem integral_rect_mul_right (hJ : RectangleMeasureModulusStatement.{u}) {k m : ℕ}
    (Ψ : Matrix (Fin k) (Fin m) (Adeles F) → ℂ) (hΨ : Continuous Ψ) (g : Points F m) :
    ∫ x, Ψ (x * ((GeneralLinearGroupPoints.adelicEquiv F m g :
        Matrix.GeneralLinearGroup (Fin m) (Adeles F)) : Matrix (Fin m) (Fin m) (Adeles F)))
        ∂rectangleMeasure F k m =
      ((detNorm F m g ^ k)⁻¹ : ℝ) • ∫ x, Ψ x ∂rectangleMeasure F k m := by
  have hφ : Continuous fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
      x * ((GeneralLinearGroupPoints.adelicEquiv F m g :
        Matrix.GeneralLinearGroup (Fin m) (Adeles F)) : Matrix (Fin m) (Fin m) (Adeles F)) :=
    continuous_id.matrix_mul continuous_const
  rw [← integral_map hφ.aemeasurable hΨ.aestronglyMeasurable, hJ F k m g, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (detNorm_pos F m g).le k))]

theorem integrable_rect_mul_right_iff (hJ : RectangleMeasureModulusStatement.{u}) {k m : ℕ}
    (Ψ : Matrix (Fin k) (Fin m) (Adeles F) → ℂ) (hΨ : Continuous Ψ) (g : Points F m) :
    Integrable (fun x => Ψ (x * ((GeneralLinearGroupPoints.adelicEquiv F m g :
        Matrix.GeneralLinearGroup (Fin m) (Adeles F)) : Matrix (Fin m) (Fin m) (Adeles F))))
        (rectangleMeasure F k m) ↔
      Integrable Ψ (rectangleMeasure F k m) := by
  have hφ : Continuous fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
      x * ((GeneralLinearGroupPoints.adelicEquiv F m g :
        Matrix.GeneralLinearGroup (Fin m) (Adeles F)) : Matrix (Fin m) (Fin m) (Adeles F)) :=
    continuous_id.matrix_mul continuous_const
  have hpos : 0 < (detNorm F m g ^ k)⁻¹ := inv_pos.mpr (pow_pos (detNorm_pos F m g) k)
  have h1 : Integrable Ψ (Measure.map (fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
        x * ((GeneralLinearGroupPoints.adelicEquiv F m g :
          Matrix.GeneralLinearGroup (Fin m) (Adeles F)) : Matrix (Fin m) (Fin m) (Adeles F)))
        (rectangleMeasure F k m)) ↔
      Integrable (Ψ ∘ fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
        x * ((GeneralLinearGroupPoints.adelicEquiv F m g :
          Matrix.GeneralLinearGroup (Fin m) (Adeles F)) : Matrix (Fin m) (Fin m) (Adeles F)))
        (rectangleMeasure F k m) :=
    integrable_map_measure hΨ.aestronglyMeasurable hφ.aemeasurable
  rw [hJ F k m g, integrable_smul_measure (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top] at h1
  exact h1.symm

end Measure

section Terms

local instance dualFinalRectMeasurableSpace' (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _
local instance dualFinalRectBorelSpace' (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

variable [CompactSpace (AdeleQuotient F)] {t k : ℕ}

omit [CompactSpace (AdeleQuotient F)] in
theorem rectangularPoint_one_cast (h : t < t + 1 + k) (v : Matrix (Fin k) (Fin (t + 1)) (Adeles F)) :
    rectangularPoint F h 1 (Matrix.of fun i j => v (Fin.cast (show t + 1 + k - (t + 1) = k by omega) i) j) =
      xcPoint F (m := t + 1) (K := k) (fun q => v q.1 q.2) 0 :=
  rectangularPoint_one h _

/-- **One unfolded term after `J`**. -/
theorem integral_rectIntegrand_eq (hJ : RectangleMeasureModulusStatement.{u}) (h : t < t + 1 + k)
    (W : Points F (t + 1 + k + 1) → ℂ) (hWc : Continuous W) (g : Points F (t + 1))
    (b : RationalGL F (t + 1)) :
    ∫ v, W (padRational F (show t + 1 ≤ t + 1 + k + 1 by omega) b *
        xcPoint F (fun q => v q.1 q.2) 0 *
          (pad F (show t + 1 ≤ t + 1 + k + 1 by omega) g * wPoint)) ∂rectangleMeasure F k (t + 1) =
      ((detNorm F (t + 1) g ^ (t + 1 + k - (t + 1)))⁻¹ : ℝ) •
        ∫ x, W (padRational F (show t + 1 ≤ t + 1 + k + 1 by omega) b *
          rectangularPoint F h g x * wPoint) ∂rectangleMeasure F (t + 1 + k - (t + 1)) (t + 1) := by
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F) → ℂ,
      Ψ = fun x => W (padRational F (show t + 1 ≤ t + 1 + k + 1 by omega) b *
        rectangularPoint F h g x * wPoint) := ⟨_, rfl⟩
  have hΨ : Continuous Ψ := by
    have hpair : Continuous fun x : Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F) =>
        ((g, x) : Points F (t + 1) × Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F)) :=
      continuous_const.prodMk continuous_id
    have hr : Continuous fun x : Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F) =>
        rectangularPoint F h g x :=
      ((continuous_rectangularPoint F h).comp hpair).congr fun _ => rfl
    rw [hΨdef]
    exact hWc.comp ((continuous_const.mul hr).mul continuous_const)
  have e1 : ∫ v, W (padRational F (show t + 1 ≤ t + 1 + k + 1 by omega) b *
        xcPoint F (fun q => v q.1 q.2) 0 *
          (pad F (show t + 1 ≤ t + 1 + k + 1 by omega) g * wPoint)) ∂rectangleMeasure F k (t + 1) =
      ∫ x, Ψ (x * ((GeneralLinearGroupPoints.adelicEquiv F (t + 1) g :
        Matrix.GeneralLinearGroup (Fin (t + 1)) (Adeles F)) :
          Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)))
        ∂rectangleMeasure F (t + 1 + k - (t + 1)) (t + 1) := by
    rw [integral_rect_cast (show t + 1 + k - (t + 1) = k by omega)]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    rw [hΨdef]
    beta_reduce
    rw [← rectangularPoint_one_mul_pad, rectangularPoint_one_cast h v]
    simp only [mul_assoc]
  rw [e1, integral_rect_mul_right hJ Ψ hΨ g, hΨdef]

/-- **One term of `E'`**, as a rectangle integral of `W̃` at a chosen coset representative. -/
theorem dualRectIntegral_cosetRep (h : t < t + 1 + k)
    (T : Automorphic.CuspidalOperatorRealization F (t + 1 + k))
    (hT : DualCuspidalWhittakerExpansion F T) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (q : RationalCosetIndex F (t + 1))
    (g : Points F (t + 1)) :
    dualRectIntegral F h (dualWhittaker F h T ψ v) (rationalCosetRep F (t + 1) q * g) =
      ∫ x, dualFunction F (t + 1 + k + 1) (cuspWhittaker F T ψ v)
        (padRational F (show t + 1 ≤ t + 1 + k + 1 by omega)
          (rationalCosetIndexEquiv F (t + 1) q).out * rectangularPoint F h g x * wPoint)
        ∂rectangleMeasure F (t + 1 + k - (t + 1)) (t + 1) := by
  have hW := dualData_dualCuspWhittaker (m := t + 1) (K := k) T hT ψ hψ v
  have hrel : QuotientGroup.rightRel (rationalUpperUnipotent F (t + 1))
      (rationalSubgroupEquiv F (t + 1) q.out) (rationalCosetIndexEquiv F (t + 1) q).out := by
    have : rationalCosetIndexEquiv F (t + 1) q =
        Quotient.mk _ (rationalSubgroupEquiv F (t + 1) q.out) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [this]
    exact Quotient.exact (Quotient.out_eq _).symm
  unfold dualRectIntegral
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [dualWhittaker, translateFunction]
  rw [rectangularPoint_mul_left, unfoldingWeyl_eq_wPoint, rationalCosetRep, cosetRep,
    pad_coe_rationalSubgroup, mul_assoc, mul_assoc,
    ← hW.padRational_of_rightRel hψ.2.2.1 _ hrel]

end Terms

section Expansion

variable [CompactSpace (AdeleQuotient F)]

omit [CompactSpace (AdeleQuotient F)] in
theorem detPower_neg_half (n : ℕ) (g : Points F n) (K : ℕ) :
    detPower F n g (-(K : ℂ) / 2) =
      detPower F n g ((K : ℂ) / 2) * (((detNorm F n g ^ K)⁻¹ : ℝ) : ℂ) := by
  have hN := detNorm_pos F n g
  have h1 : ((detNorm F n g ^ K)⁻¹ : ℝ) = Real.exp (-(K * Real.log (detNorm F n g))) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hN]
  rw [h1, Complex.ofReal_exp]
  simp only [detPower, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [CompactSpace (AdeleQuotient F)] in
theorem exists_addChar_ne_one {ψ : AddChar (Adeles F) ℂ} (hψ : ψ ≠ 1) :
    ∀ a : F, a ≠ 0 → ∃ y : Adeles F, ψ (algebraMap F (Adeles F) a * y) ≠ 1 := by
  intro a ha
  have hnot : ¬ ∀ z, ψ z = 1 := fun hall =>
    hψ (DFunLike.ext _ _ fun z => by rw [hall z, AddChar.one_apply])
  obtain ⟨z, hz⟩ := not_forall.mp hnot
  refine ⟨algebraMap F (Adeles F) a⁻¹ * z, ?_⟩
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  exact hz

/-- **Premise E' from `J` and the dual Whittaker expansion.** -/
theorem dualProjectionWhittakerExpansion_of_dualCuspidalWhittakerExpansion
    (hJ : RectangleMeasureModulusStatement.{u}) {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (hT : DualCuspidalWhittakerExpansion F T) :
    DualProjectionWhittakerExpansion F h T := by
  obtain ⟨k, rfl⟩ : ∃ k, r = t + 1 + k := ⟨r - (t + 1), by omega⟩
  intro ψ hψ v g
  have hψF := hψ.2.2.1
  have hψc := hψ.1
  have hψ1 := hψ.2.2.2
  have hψn := exists_addChar_ne_one hψ.2.1
  have hW := dualData_dualCuspWhittaker (m := t + 1) (K := k) T hT ψ hψ v
  have hWc := hW.continuous
  have hWΓ : ∀ k' ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1 + k + 1)), ∀ x,
      cornerSum F (t + 1) k (dualFunction F (t + 1 + k + 1) (cuspWhittaker F T ψ v)) (k' * x) =
        cornerSum F (t + 1) k (dualFunction F (t + 1 + k + 1) (cuspWhittaker F T ψ v)) x := by
    intro k' hk' x
    rw [cornerSum_dualCuspWhittaker T hT ψ hψ v, cornerSum_dualCuspWhittaker T hT ψ hψ v]
    exact dualCuspFunction_rational_mul F T v hk' x
  obtain ⟨y, hy⟩ : ∃ y : Points F (t + 1 + k + 1),
      y = pad F (show t + 1 ≤ t + 1 + k + 1 by omega) g * wPoint := ⟨_, rfl⟩
  have hsum := hW.hasSum_integral_rectIntegrand hψF y
  -- the right-hand side
  have hRHS : dualProjection F (Nat.succ_lt_succ h) ψ (dualFunction F (t + 1 + k + 1)
      (cuspFunction F T v)) (pad F (Nat.le_succ (t + 1)) g) =
      detPower F (t + 1) g (((t + 1 + k - (t + 1) : ℕ) : ℂ) / 2) *
        dualRectT k (dualFunction F (t + 1 + k + 1) (cuspWhittaker F T ψ v)) y := by
    have hfun : (fun g' => dualFunction F (t + 1 + k + 1) (cuspFunction F T v)
        (iota F (t + 1 + k + 1) g')) = fun g' =>
          cornerSum F (t + 1) k (dualFunction F (t + 1 + k + 1) (cuspWhittaker F T ψ v))
            (iota F (t + 1 + k + 1) g') :=
      funext fun g' => (cornerSum_dualCuspWhittaker T hT ψ hψ v _).symm
    unfold dualProjection projection
    rw [UnequalAnalytic.iota_pad, UnequalAnalytic.detPower_pad, UnequalAnalytic.detPower_iota,
      UnequalAnalytic.pad_pad, hfun, hW.coefficient_eq_dualPeriod hψF hψc hψ1 hWΓ,
      UnequalAnalytic.iota_pad, UnequalAnalytic.iota_iota,
      dualPeriod_eq_dualRectT ψ hψF hψc hψ1 hψn k _ hW, wPoint_mul_pad, ← hy, neg_div, neg_neg]
  refine ⟨?_, ?_⟩
  · -- integrability
    obtain ⟨p₀, hp₀⟩ : ∃ p₀ : UnipotentRationalCosets F (t + 1), p₀ = Quotient.mk _ 1 :=
      ⟨_, rfl⟩
    have hrel₀ : QuotientGroup.rightRel (rationalUpperUnipotent F (t + 1)) 1 p₀.out := by
      rw [hp₀]
      exact (QuotientGroup.rightRel _).iseqv.symm (Quotient.exact (Quotient.out_eq _))
    have hint := (hW.integral_rectIntegrand hψF y p₀).1
    have h1 : Integrable (fun x : Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F) =>
        dualFunction F (t + 1 + k + 1) (cuspWhittaker F T ψ v)
          (padRational F (show t + 1 ≤ t + 1 + k + 1 by omega) p₀.out *
            rectangularPoint F h 1 x * y)) (rectangleMeasure F (t + 1 + k - (t + 1)) (t + 1)) := by
      rw [integrable_rect_cast (show t + 1 + k - (t + 1) = k by omega)]
      refine hint.congr (ae_of_all _ fun v => ?_)
      unfold rectIntegrand
      beta_reduce
      rw [rectangularPoint_one_cast h v]
    have hΨc : Continuous fun x : Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F) =>
        dualFunction F (t + 1 + k + 1) (cuspWhittaker F T ψ v)
          (padRational F (show t + 1 ≤ t + 1 + k + 1 by omega) p₀.out *
            rectangularPoint F h g x * wPoint) := by
      have hpair : Continuous fun x : Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F) =>
          ((g, x) : Points F (t + 1) ×
            Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F)) :=
        continuous_const.prodMk continuous_id
      have hr : Continuous fun x : Matrix (Fin (t + 1 + k - (t + 1))) (Fin (t + 1)) (Adeles F) =>
          rectangularPoint F h g x :=
        ((continuous_rectangularPoint F h).comp hpair).congr fun _ => rfl
      exact hWc.comp ((continuous_const.mul hr).mul continuous_const)
    have h2 := (integrable_rect_mul_right_iff hJ _ hΨc g).mp (h1.congr (ae_of_all _ fun x => by
      beta_reduce
      rw [hy, ← mul_assoc, mul_assoc (padRational F _ _), rectangularPoint_one_mul_pad]))
    refine h2.congr (ae_of_all _ fun x => ?_)
    simp only [dualWhittaker, translateFunction, unfoldingWeyl_eq_wPoint]
    rw [mul_assoc, hW.padRational_of_rightRel hψF _ hrel₀]
    simp [padRational]
  · -- the expansion
    rw [hRHS]
    rw [← (rationalCosetIndexEquiv F (t + 1)).hasSum_iff] at hsum
    have := hsum.mul_left (detPower F (t + 1) g (((t + 1 + k - (t + 1) : ℕ) : ℂ) / 2))
    convert this using 1
    funext q
    simp only [Function.comp_apply]
    rw [dualRectIntegral_cosetRep h T hT ψ hψ v q g]
    unfold rectIntegrand
    rw [hy, integral_rectIntegrand_eq hJ h _ hWc g, detPower_neg_half, Complex.real_smul]
    ring

end Expansion

end Langlands.Global.RankinSelbergGlobal.Unfolding
