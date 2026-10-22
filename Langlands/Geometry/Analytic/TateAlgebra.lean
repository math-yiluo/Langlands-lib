import Mathlib.RingTheory.MvPowerSeries.Restricted
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.Basic

/-! # Strict Tate algebras from restricted multivariate power series -/

noncomputable section

universe u v

namespace Langlands.Analytic

open Filter
open scoped Topology ZeroAtInfty

/-- The exponent set with its discrete topology, isolated from any topology on
the variable type. -/
def MonomialIndex (σ : Type u) := σ →₀ ℕ

instance (σ : Type u) : TopologicalSpace (MonomialIndex σ) := ⊥
instance (σ : Type u) : DiscreteTopology (MonomialIndex σ) := ⟨rfl⟩

section GeneralCoefficients

variable (σ : Type u) (K : Type v) [NormedCommRing K] [IsUltrametricDist K]

/-- The genuine subalgebra of coefficient sequences tending to zero. -/
def restrictedSubalgebra : Subalgebra K (MvPowerSeries σ K) where
  __ := MvPowerSeries.IsRestricted.subring (fun _ : σ => (1 : ℝ))
  algebraMap_mem' a := MvPowerSeries.isRestricted_C _ a

/-- Restricted power series of polyradius one. For `σ = Fin n` this is the
strict Tate algebra in `n` variables. -/
def StrictTateAlgebra := ↥(restrictedSubalgebra σ K)

namespace StrictTateAlgebra

instance : CommRing (StrictTateAlgebra σ K) :=
  inferInstanceAs (CommRing ↥(restrictedSubalgebra σ K))

instance : Algebra K (StrictTateAlgebra σ K) :=
  inferInstanceAs (Algebra K ↥(restrictedSubalgebra σ K))

instance [Nontrivial K] : Nontrivial (StrictTateAlgebra σ K) :=
  inferInstanceAs (Nontrivial ↥(restrictedSubalgebra σ K))

/-- The actual underlying formal power series. -/
def series (f : StrictTateAlgebra σ K) : MvPowerSeries σ K := f.val

/-- The coefficient map into the complete supremum-norm space of functions
vanishing at infinity. Multiplication on the Tate algebra remains convolution. -/
def coefficients (f : StrictTateAlgebra σ K) : C₀(MonomialIndex σ, K) where
  toFun t := MvPowerSeries.coeff t (series σ K f)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite]
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    have hf := f.property
    change MvPowerSeries.IsRestricted (fun _ : σ => (1 : ℝ)) f.val at hf
    simpa [MvPowerSeries.IsRestricted, Finsupp.prod, series, MonomialIndex] using hf

/-- Coefficients give an additive homomorphism. -/
def coefficientHom : StrictTateAlgebra σ K →+ C₀(MonomialIndex σ, K) where
  toFun := coefficients σ K
  map_zero' := by
    ext t
    exact MvPowerSeries.coeff_zero t
  map_add' f g := by
    ext t
    exact map_add (MvPowerSeries.coeff t) f.val g.val

private theorem coefficientHom_injective : Function.Injective (coefficientHom σ K) := by
  intro f g h
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro t
  exact DFunLike.congr_fun h t

/-- Every coefficient function vanishing at infinity is a restricted series. -/
def fromCoefficients (f : C₀(MonomialIndex σ, K)) : StrictTateAlgebra σ K :=
  ⟨fun t => f t, by
    change MvPowerSeries.IsRestricted (fun _ : σ => (1 : ℝ)) _
    have hf := (tendsto_zero_iff_norm_tendsto_zero).mp (zero_at_infty f)
    rw [Filter.cocompact_eq_cofinite] at hf
    simp only [MvPowerSeries.IsRestricted, Finsupp.prod, one_pow,
      Finset.prod_const_one, mul_one]
    change Tendsto (fun t : MonomialIndex σ => ‖f t‖) cofinite (𝓝 0)
    exact hf⟩

/-- The additive equivalence of restricted series with coefficient functions
vanishing at infinity. It is not a ring equivalence for pointwise multiplication. -/
def coefficientEquiv : StrictTateAlgebra σ K ≃+ C₀(MonomialIndex σ, K) where
  __ := coefficientHom σ K
  invFun := fromCoefficients σ K
  left_inv _ := rfl
  right_inv f := by ext t; rfl

instance : NormedAddCommGroup (StrictTateAlgebra σ K) :=
  NormedAddCommGroup.induced _ _ (coefficientHom σ K) (coefficientHom_injective σ K)

theorem norm_coeff_le (f : StrictTateAlgebra σ K) (t : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff t (series σ K f)‖ ≤ ‖f‖ :=
  BoundedContinuousFunction.norm_coe_le_norm (coefficients σ K f).toBCF t

theorem norm_le_iff (f : StrictTateAlgebra σ K) {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ t, ‖MvPowerSeries.coeff t (series σ K f)‖ ≤ C :=
  BoundedContinuousFunction.norm_le hC

private theorem mul_norm_le (f g : StrictTateAlgebra σ K) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  classical
  apply (norm_le_iff σ K (f * g) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro t
  change ‖MvPowerSeries.coeff t (f.val * g.val)‖ ≤ _
  rw [MvPowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro ij _
  exact (norm_mul_le _ _).trans
    (mul_le_mul (norm_coeff_le σ K f ij.1) (norm_coeff_le σ K g ij.2)
      (norm_nonneg _) (norm_nonneg _))

instance : NormedCommRing (StrictTateAlgebra σ K) :=
  { (inferInstance : NormedAddCommGroup (StrictTateAlgebra σ K)),
    (inferInstance : CommRing (StrictTateAlgebra σ K)) with
    norm_mul_le := mul_norm_le σ K }

/-- The Gauss norm restricts to the given norm on the coefficient ring. -/
theorem norm_algebraMap (c : K) :
    ‖algebraMap K (StrictTateAlgebra σ K) c‖ = ‖c‖ := by
  classical
  apply le_antisymm
  · apply (norm_le_iff σ K _ (norm_nonneg c)).mpr
    intro t
    change ‖MvPowerSeries.coeff t (MvPowerSeries.C c)‖ ≤ ‖c‖
    rw [MvPowerSeries.coeff_C]
    split_ifs <;> simp
  · have h := norm_coeff_le σ K (algebraMap K (StrictTateAlgebra σ K) c) 0
    change ‖MvPowerSeries.coeff 0 (MvPowerSeries.C c)‖ ≤ _ at h
    simpa using h

instance [NormOneClass K] : NormOneClass (StrictTateAlgebra σ K) where
  norm_one := by simpa using norm_algebraMap σ K (1 : K)

instance : IsUltrametricDist (StrictTateAlgebra σ K) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g => by
    apply (norm_le_iff σ K (f + g)
      ((norm_nonneg f).trans (le_max_left _ _))).mpr
    intro t
    change ‖MvPowerSeries.coeff t (f.val + g.val)‖ ≤ _
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (norm_coeff_le σ K f t) (norm_coeff_le σ K g t))

/-- Coefficients preserve the actual norm and metric. -/
def coefficientIsometry : StrictTateAlgebra σ K ≃ᵢ C₀(MonomialIndex σ, K) where
  __ := coefficientEquiv σ K
  isometry_toFun := by
    intro f g
    rfl

instance [CompleteSpace K] : CompleteSpace (StrictTateAlgebra σ K) :=
  (coefficientIsometry σ K).completeSpace_iff.mpr inferInstance

end StrictTateAlgebra

end GeneralCoefficients

namespace StrictTateAlgebra

variable (σ : Type u) (K : Type v) [NormedField K] [IsUltrametricDist K]

instance : NormedAlgebra K (StrictTateAlgebra σ K) where
  norm_smul_le c f := by
    apply (norm_le_iff σ K (c • f) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    intro t
    change ‖MvPowerSeries.coeff t (c • f.val)‖ ≤ _
    rw [MvPowerSeries.coeff_smul, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_coeff_le σ K f t) (norm_nonneg _)

end StrictTateAlgebra

end Langlands.Analytic
