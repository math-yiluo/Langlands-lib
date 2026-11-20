import Langlands.Global.RankinSelberg.ComplexGodementColumnChange
import Langlands.Global.RankinSelberg.ComplexGodementSection
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra
import Langlands.Representation.Shahidi.UnipotentProduct

/-! # Godement's section in the open-cell Jacquet integral -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix
open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Shahidi (unipotentProduct unipotentProductMeasure)

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementJacquetComparison

open ComplexGodement (trailingRows characterWeight normPower godementSection godementSectionIntegrand)
open ComplexGodementColumnChange (columnIntegral iteratedKernel)
open ArchimedeanLocal (complexNormalizedAbs)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC det_upperUnipotent)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "U" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Col" => Fin (r + 1) → ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "w" => weylLong (r + 1) ℂ
local notation "w'" => weylLong (r + 1 + 1) ℂ

private theorem det_unipotent {n : ℕ} (u : GeneralLinear.upperUnipotent n ℂ) :
    determinant u.val = 1 :=
  Units.ext (det_upperUnipotent u)

private theorem characterWeight_detPower {n : ℕ} (d : ComplexCharacterData) (s : ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    characterWeight d s (determinant g) = (d.character (determinant g) : ℂ) *
      ArchimedeanLocal.detPower complexNormalizedAbs g s := by
  have hn : 0 < complexNormalizedAbs g.val.det := by
    unfold complexNormalizedAbs
    exact pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) _
  change (d.character (determinant g) : ℂ) * ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ s = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'), ← Complex.ofReal_log hn.le]
  simp only [ArchimedeanLocal.detPower, mul_comm (↑(Real.log (complexNormalizedAbs g.val.det))) s]

private theorem normPower_weyl (s : ℂ) (n : ℕ) : normPower s (determinant (weylLong n ℂ)) = 1 := by
  induction n with
  | zero =>
    have h : determinant (weylLong 0 ℂ) = 1 := Units.ext (by simp [Matrix.det_fin_zero])
    rw [h, map_one]
  | succ n ih =>
    rw [Langlands.RankinSelberg.RankOneGammaTwist.determinant_weylLong_succ, map_mul,
      map_pow, ih, mul_one]
    have h : normPower s (-1 : ℂˣ) = 1 := by simp [normPower, normSqC]
    rw [h, one_pow]

private theorem characterWeight_weyl (d : ComplexCharacterData) (s : ℂ) (n : ℕ) :
    characterWeight d s (determinant (weylLong n ℂ)) =
      (d.character (determinant (weylLong n ℂ)) : ℂ) := by
  change (d.character _ : ℂ) * normPower s (determinant (weylLong n ℂ)) = _
  rw [normPower_weyl, mul_one]

private theorem weylWeight (d : ComplexCharacterData) (s t : ℂ) :
    characterWeight d s (determinant w') * characterWeight d t (determinant w) =
      (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) := by
  rw [characterWeight_weyl, characterWeight_weyl,
    Langlands.RankinSelberg.RankOneGammaTwist.determinant_weylLong_succ,
    ← Units.val_mul, ← map_mul, mul_assoc, ← map_mul, weylLong_mul_self, map_one, mul_one]

/-- The first-superdiagonal character splits in ordered upper-left and column coordinates. -/
theorem character_unipotentProduct (a : ℂˣ) (u : U) (v : Col) :
    complexWhittakerCharacter a (unipotentProduct (u, v)).val =
      complexWhittakerCharacter a u.val * (complexScaledCharacter a).complex (v (Fin.last r)) := by
  have hv : (u.val.val *ᵥ v) (Fin.last r) = v (Fin.last r) := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last r)]
    · rw [UpperUnipotent.entry_diag, one_mul]
    · intro j _ hj
      rw [UpperUnipotent.entry_eq_zero u (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
    · simp
  unfold complexWhittakerCharacter
  rw [Fin.sum_univ_castSucc, ← AddChar.map_add_eq_mul]
  congr 1
  rw [show (Fin.last r).succ = Fin.last (r + 1) by rfl, Langlands.Shahidi.unipotentProduct_column, hv]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show i.castSucc.succ = i.succ.castSucc by rfl, Langlands.Shahidi.unipotentProduct_left]

private theorem mul_rectangularJoin_one (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (v : Col) :
    A * rectangularJoin 1 v = rectangularJoin A (A *ᵥ v) := by
  ext i j
  induction j using Fin.lastCases with
  | last =>
    rw [rectangularJoin_last, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    simp only [rectangularJoin_last]
  | cast j =>
    rw [rectangularJoin_castSucc, Matrix.mul_apply]
    simp only [rectangularJoin_castSucc, ← Matrix.mul_apply, Matrix.mul_one]

private theorem trailingRows_weyl_product (u : U) (v : Col) (g : G') :
    trailingRows (w' * (unipotentProduct (u, v)).val * g).val =
      (w).val * (u.val.val * rectangularJoin 1 v) * g.val := by
  have hrows : trailingRows (w' * (unipotentProduct (u, v)).val).val =
      (w).val * (u.val.val * rectangularJoin 1 v) := by
    ext i j
    change (w' * (unipotentProduct (u, v)).val) i.succ j = _
    rw [weylLong_mul_entry, Fin.rev_succ, Langlands.RankinSelberg.weylLong_mul_apply,
      mul_rectangularJoin_one]
    induction j using Fin.lastCases with
    | last => rw [Langlands.Shahidi.unipotentProduct_column, rectangularJoin_last]
    | cast j => rw [Langlands.Shahidi.unipotentProduct_left, rectangularJoin_castSucc]
  change ((w' * (unipotentProduct (u, v)).val).val * g.val).submatrix Fin.succ id = _
  rw [Matrix.submatrix_mul _ _ Fin.succ id id Function.bijective_id, ← trailingRows, hrows]
  rfl

/-- The open-cell integral in the upper-Borel convention. The parameter `a` belongs
to the integrating character. Absolute convergence and right invariance of `dn`
give left character `-a` by right translation of the unipotent variable. -/
def openCellIntegral {j : ℕ} (a : ℂˣ) (dn : Measure (GeneralLinear.upperUnipotent (j + 1) ℂ))
    (f : Langlands.GeneralLinear (j + 1) ℂ → ℂ) (g : Langlands.GeneralLinear (j + 1) ℂ) : ℂ :=
  ∫ u, f (weylLong (j + 1) ℂ * u.val * g) * complexWhittakerCharacter a u.val ∂dn

/-- The joint integration kernel for the open-cell Godement integral after splitting
 the large unipotent variable into its upper-left block and last column. -/
def jointKernel (d : ComplexCharacterData) (a : ℂˣ) (Φ : Rect → ℂ) (f : G → ℂ) (g : G')
    (p : (U × Col) × G) : ℂ :=
  godementSectionIntegrand d Φ f (w' * (unipotentProduct p.1).val * g) p.2 *
    complexWhittakerCharacter a (unipotentProduct p.1).val

private def shiftedCoordinates : ((U × Col) × G) ≃ᵐ ((U × Col) × G) where
  toFun p := (p.1, p.2 * (w * p.1.1.val))
  invFun p := (p.1, p.2 * (w * p.1.1.val)⁻¹)
  left_inv p := Prod.ext rfl (mul_inv_cancel_right _ _)
  right_inv p := Prod.ext rfl (inv_mul_cancel_right _ _)
  measurable_toFun := by
    change Measurable (fun p : (U × Col) × G => (p.1, p.2 * (w * p.1.1.val)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : (U × Col) × G => (p.1, p.2 * (w * p.1.1.val)⁻¹))
    fun_prop

private theorem measurePreserving_shiftedCoordinates (dp : Measure (U × Col)) (ν : Measure G)
    [SFinite dp] [SFinite ν] [ν.IsMulRightInvariant] :
    MeasurePreserving shiftedCoordinates (dp.prod ν) (dp.prod ν) :=
  (MeasurePreserving.id dp).skew_product shiftedCoordinates.measurable.snd
    (ae_of_all _ fun p => (measurePreserving_mul_right ν (w * p.1.val)).map_eq)

private def columnFactor (a : ℂˣ) (Φ : Rect → ℂ) (g : G') (h : G) (v : Col) : ℂ :=
  Φ (h.val * rectangularJoin 1 v * g.val) * (complexScaledCharacter a).complex (v (Fin.last r))

private def splitKernel (d : ComplexCharacterData) (a : ℂˣ) (Φ : Rect → ℂ)
    (f : G → ℂ) (g : G') (p : (U × Col) × G) : ℂ :=
  (f (w * p.1.1.val * p.2⁻¹) * complexWhittakerCharacter a p.1.1.val) *
    columnFactor a Φ g p.2 p.1.2 * characterWeight d (((r + 1 : ℕ) + 1 : ℂ) / 2) (determinant p.2)

private theorem jointKernel_eq (d : ComplexCharacterData) (a : ℂˣ) (Φ : Rect → ℂ)
    (f : G → ℂ) (g : G') (p : (U × Col) × G) :
    jointKernel d a Φ f g p =
      characterWeight d (((r + 1 : ℕ) + 1 : ℂ) / 2) (determinant w) *
        splitKernel d a Φ f g (shiftedCoordinates p) := by
  rcases p with ⟨⟨u, v⟩, h⟩
  unfold jointKernel godementSectionIntegrand
  rw [character_unipotentProduct, trailingRows_weyl_product]
  have hrow : h.val * ((w).val * (u.val.val * rectangularJoin 1 v) * g.val) =
      (h * (w * u.val)).val * rectangularJoin 1 v * g.val := by
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [hrow, show shiftedCoordinates ((u, v), h) = ((u, v), h * (w * u.val)) from rfl]
  dsimp only [splitKernel, columnFactor]
  have hi : w * u.val * (h * (w * u.val))⁻¹ = h⁻¹ := by rw [mul_inv_rev, mul_inv_cancel_left]
  have hw :
      characterWeight d (((r + 1 : ℕ) + 1 : ℂ) / 2) (determinant w) *
        characterWeight d (((r + 1 : ℕ) + 1 : ℂ) / 2) (determinant (h * (w * u.val))) =
        characterWeight d (((r + 1 : ℕ) + 1 : ℂ) / 2) (determinant h) := by
    rw [← map_mul, map_mul determinant h, map_mul determinant w, det_unipotent, mul_one,
      mul_comm (determinant h), ← mul_assoc, ← map_mul, weylLong_mul_self, map_one, one_mul]
  rw [hi, ← hw]
  ring

variable (r) in
/-- The comparison (7.6) on the absolutely integrable joint kernel, with upper-Borel
 inducing functions and the supplied product measure on the large unipotent group. -/
def ComplexGodementOpenCellComparisonStatement : Prop :=
  ∀ (ν : Measure G) [SFinite ν] [ν.IsMulRightInvariant] (dn : Measure U) [SFinite dn]
    (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData) (a : ℂˣ)
    (Φ : Rect → ℂ) (f : G → ℂ) (g : G'),
    Integrable (jointKernel d a Φ f g) ((dn.prod (rowMeasure μ (r + 1))).prod ν) →
    openCellIntegral a (unipotentProductMeasure dn (rowMeasure μ (r + 1)))
        (godementSection ν d Φ f) g =
      (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
        characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant g) *
          ∫ h, iteratedKernel (complexScaledCharacter a) μ d (fun X => Φ (X * g.val))
            (openCellIntegral a dn f) (((r + 1 : ℕ) + 1 : ℂ) / 2) h ∂ν

theorem openCellIntegral_godementSection : ComplexGodementOpenCellComparisonStatement r := by
  intro ν hν hright dn hdn μ d a Φ f g hjoint
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  let dp := dn.prod (rowMeasure μ (r + 1))
  let s : ℂ := (((r + 1 : ℕ) : ℂ) / 2)
  let t : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2)
  let c := characterWeight d t (determinant w)
  let K := splitKernel d a Φ f g
  let J := jointKernel d a Φ f g
  have hKc : Integrable (fun p => c * K p) (dp.prod ν) := by
    refine ((measurePreserving_shiftedCoordinates dp ν).integrable_comp_emb
      shiftedCoordinates.measurableEmbedding).mp ?_
    exact hjoint.congr (ae_of_all _ (jointKernel_eq d a Φ f g))
  have hc : c ≠ 0 := by
    rw [show c = (d.character (determinant w) : ℂ) from characterWeight_weyl d t (r + 1)]
    exact (d.character (determinant w)).ne_zero
  have hK := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) K).mp hKc
  have hJ : (∫ p, J p ∂dp.prod ν) = c * (∫ p, K p ∂dp.prod ν) := by
    simp only [J, jointKernel_eq, ← integral_const_mul]
    exact (measurePreserving_shiftedCoordinates dp ν).integral_comp' (fun p => c * K p)
  have hlarge : openCellIntegral a (unipotentProductMeasure dn (rowMeasure μ (r + 1)))
        (godementSection ν d Φ f) g =
      characterWeight d s (determinant w') * characterWeight d s (determinant g) * ∫ p, J p ∂dp.prod ν := by
    unfold openCellIntegral
    rw [Langlands.Shahidi.integral_unipotentProductMeasure, integral_prod J hjoint, ← integral_const_mul]
    apply integral_congr_ae (ae_of_all _ fun p => ?_)
    unfold godementSection J jointKernel
    dsimp only
    rw [map_mul determinant, map_mul determinant, det_unipotent, mul_one, map_mul,
      integral_mul_const]
    ring
  have hiter : (∫ p, K p ∂dp.prod ν) =
      ∫ h, iteratedKernel (complexScaledCharacter a) μ d (fun X => Φ (X * g.val))
            (openCellIntegral a dn f) t h ∂ν := by
    rw [integral_prod_symm K hK]
    apply integral_congr_ae (ae_of_all _ fun h => ?_)
    dsimp only [K, splitKernel]
    rw [integral_mul_const, integral_prod_mul
      (fun u : U => f (w * u.val * h⁻¹) * complexWhittakerCharacter a u.val)
      (columnFactor a Φ g h)]
    unfold iteratedKernel columnFactor columnIntegral openCellIntegral
    simp only [mul_rectangularJoin_one, characterWeight_detPower, t]
    ring
  rw [hlarge, hJ, hiter]
  change (characterWeight d s (determinant w') * characterWeight d s (determinant g)) *
      (c * _) = _
  rw [mul_mul_mul_comm, weylWeight d s t]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexGodementJacquetComparison
