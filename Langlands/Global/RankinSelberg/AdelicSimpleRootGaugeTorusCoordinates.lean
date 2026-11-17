import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugePadding

/-! # Torus coordinates for a proper padded block -/

noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace GaugeTorusCoordinates

variable {G : Type v} [CommGroup G]

/-- Adjacent ratios followed by the last diagonal entry. -/
def blockRoots (t : ℕ) (d : Fin (t + 1) → G) : Fin (t + 1) → G :=
  Fin.lastCases (d (Fin.last t)) (fun i => d i.castSucc / d i.succ)

@[simp]
theorem blockRoots_last (t : ℕ) (d : Fin (t + 1) → G) :
    blockRoots t d (Fin.last t) = d (Fin.last t) := by
  simp [blockRoots]

@[simp]
theorem blockRoots_castSucc (t : ℕ) (d : Fin (t + 1) → G) (i : Fin t) :
    blockRoots t d i.castSucc = d i.castSucc / d i.succ := by
  simp [blockRoots]

/-- Recover each diagonal entry by multiplying its remaining roots. -/
def tailProducts (t : ℕ) (a : Fin (t + 1) → G) : Fin (t + 1) → G :=
  fun i => ∏ j ∈ Finset.Ici i, a j

@[simp]
theorem tailProducts_last (t : ℕ) (a : Fin (t + 1) → G) :
    tailProducts t a (Fin.last t) = a (Fin.last t) := by
  simp only [tailProducts, ← Fin.top_eq_last, Finset.Ici_top, Finset.prod_singleton]

theorem tailProducts_castSucc (t : ℕ) (a : Fin (t + 1) → G) (i : Fin t) :
    tailProducts t a i.castSucc = a i.castSucc * tailProducts t a i.succ := by
  have hI : Finset.Ici i.castSucc = insert i.castSucc (Finset.Ici i.succ) := by
    ext j
    simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_def, Fin.ext_iff,
      Fin.val_castSucc, Fin.val_succ]
    omega
  simp only [tailProducts, hI]
  rw [Finset.prod_insert]
  simp only [Finset.mem_Ici, Fin.le_def, Fin.val_castSucc, Fin.val_succ]
  omega

theorem tailProducts_blockRoots (t : ℕ) (d : Fin (t + 1) → G) :
    tailProducts t (blockRoots t d) = d := by
  funext i
  induction i using Fin.reverseInduction with
  | last => simp
  | cast i ih =>
    rw [tailProducts_castSucc, blockRoots_castSucc, ih, div_mul_cancel]

theorem blockRoots_tailProducts (t : ℕ) (a : Fin (t + 1) → G) :
    blockRoots t (tailProducts t a) = a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · rw [blockRoots_castSucc, tailProducts_castSucc, mul_div_cancel_right]

/-- Simple roots and the final diagonal coordinate give a multiplicative
coordinate system on the whole diagonal torus. -/
def blockRootEquiv (t : ℕ) : (Fin (t + 1) → G) ≃* (Fin (t + 1) → G) where
  toFun := blockRoots t
  invFun := tailProducts t
  left_inv := tailProducts_blockRoots t
  right_inv := blockRoots_tailProducts t
  map_mul' d e := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp only [blockRoots_castSucc, Pi.mul_apply, mul_div_mul_comm]

/-- Multiplying the diagonal entries weights the j-th root by j + 1. -/
theorem prod_tailProducts (t : ℕ) (a : Fin (t + 1) → G) :
    ∏ i, tailProducts t a i = ∏ j, a j ^ ((j : ℕ) + 1) := by
  simp only [tailProducts, ← Finset.filter_le_eq_Ici]
  simp_rw [Finset.prod_filter]
  rw [Finset.prod_comm]
  simp_rw [← Finset.prod_filter]
  simp only [Finset.filter_ge_eq_Iic, Finset.prod_const, Fin.card_Iic]

theorem prod_eq_prod_blockRoots_pow (t : ℕ) (d : Fin (t + 1) → G) :
    ∏ i, d i = ∏ j, blockRoots t d j ^ ((j : ℕ) + 1) := by
  simpa only [tailProducts_blockRoots] using prod_tailProducts t (blockRoots t d)

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The block root coordinate map and its inverse are continuous. -/
def blockRootContinuousEquiv (t : ℕ) :
    (Fin (t + 1) → G) ≃ₜ* (Fin (t + 1) → G) where
  toMulEquiv := blockRootEquiv t
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [blockRootEquiv, blockRoots_last] using
        (continuous_apply (Fin.last t) : Continuous (fun d : Fin (t + 1) → G =>
          d (Fin.last t)))
    · simp only [blockRootEquiv, blockRoots_castSucc]
      convert!
        (continuous_apply j.castSucc : Continuous (fun d : Fin (t + 1) → G =>
          d j.castSucc)).div'
        (continuous_apply j.succ : Continuous (fun d : Fin (t + 1) → G => d j.succ)) using 1
  continuous_invFun := by
    apply continuous_pi
    intro i
    change Continuous (fun a : Fin (t + 1) → G => ∏ j ∈ Finset.Ici i, a j)
    exact continuous_finsetProd _ fun j _ => continuous_apply j

/-- A block root change of variables preserves finiteness of the lower integral
for any Haar normalization on this torus. -/
theorem lintegral_blockRoots_lt_top_iff
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (t : ℕ) (mu : Measure (Fin (t + 1) → G)) [Measure.IsHaarMeasure mu]
    (f : (Fin (t + 1) → G) → ℝ≥0∞) :
    (∫⁻ d, f (blockRoots t d) ∂mu) < ⊤ ↔ (∫⁻ a, f a ∂mu) < ⊤ := by
  let e := blockRootContinuousEquiv (G := G) t
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure (mu.map e) mu
  have hm := Measure.isMulLeftInvariant_eq_smul (mu.map e) mu
  change (∫⁻ d, f (e d) ∂mu) < ⊤ ↔ _
  erw [← lintegral_map_equiv f e.toHomeomorph.toMeasurableEquiv]
  change (∫⁻ a, f a ∂mu.map e) < ⊤ ↔ _
  rw [hm, lintegral_smul_measure]
  exact ENNReal.nnreal_smul_lt_top_iff hc.ne'

end Topology

end GaugeTorusCoordinates

variable (F : Type u) [Field F] [NumberField F]

/-- The t + 1 nonconstant simple roots of a proper padded diagonal. -/
def gaugeBlockRootIdeles (t : ℕ) (d : Fin (t + 1) → Ideles F) :
    Fin (t + 1) → Ideles F :=
  GaugeTorusCoordinates.blockRoots t d

/-- The actual determinant norm of a diagonal point is the product of its
diagonal idele norms. -/
theorem detNorm_gaugeDiagonalPoint (n : ℕ) (d : Fin n → Ideles F) :
    detNorm F n (gaugeDiagonalPoint F n d) =
      ∏ i, ((IdeleAbsoluteValue.full F (d i) : ℝ≥0) : ℝ) := by
  have hd : Matrix.GeneralLinearGroup.det
      (GeneralLinearGroupPoints.adelicEquiv F n (gaugeDiagonalPoint F n d)) =
        ∏ i, d i := by
    apply Units.ext
    simp only [gaugeDiagonalPoint, MulEquiv.apply_symm_apply,
      Matrix.GeneralLinearGroup.val_det_apply,
      GroupScheme.GeneralLinear.diagonalMatrixUnits_val, Matrix.det_diagonal, Units.coe_prod]
  change ((IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det
    (GeneralLinearGroupPoints.adelicEquiv F n (gaugeDiagonalPoint F n d))) : ℝ≥0) : ℝ) = _
  rw [hd, map_prod, Units.coe_prod, NNReal.coe_prod]

/-- In block simple-root coordinates, determinant norm has weights 1, …, t + 1. -/
theorem detNorm_gaugeDiagonalPoint_blockRoots (t : ℕ) (d : Fin (t + 1) → Ideles F) :
    detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d) =
      ∏ j, ((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^
        ((j : ℕ) + 1) := by
  rw [detNorm_gaugeDiagonalPoint]
  have hp := congrArg
    (fun a : Ideles F => ((IdeleAbsoluteValue.full F a : ℝ≥0) : ℝ))
    (GaugeTorusCoordinates.prod_eq_prod_blockRoots_pow t d)
  simpa only [gaugeBlockRootIdeles, map_prod, map_pow, Units.coe_prod,
    Units.val_pow_eq_pow_val, NNReal.coe_prod, NNReal.coe_pow] using hp

end Langlands.Global.RankinSelbergGlobal
