import Langlands.Geometry.Analytic.TateAlgebra
import Mathlib.RingTheory.MvPowerSeries.GaussNorm
import Mathlib.Topology.Order.Bornology

/-! # Restricted power series with positive polyradii -/

noncomputable section

universe u v

namespace Langlands.Analytic

/-- Positive real radii, without a condition on the coefficient value group. -/
structure PositivePolyradius (σ : Type u) where
  radius : σ → ℝ
  positive : ∀ i, 0 < radius i

namespace PositivePolyradius

instance {σ : Type u} : CoeFun (PositivePolyradius σ) (fun _ => σ → ℝ) :=
  ⟨radius⟩

/-- The polyradius with every radius equal to one. -/
def unit (σ : Type u) : PositivePolyradius σ := ⟨fun _ => 1, fun _ => zero_lt_one⟩

@[simp] theorem unit_apply {σ : Type u} (i : σ) : unit σ i = 1 := rfl

/-- The positive weight attached to a finitely supported exponent. -/
def weight {σ : Type u} (r : PositivePolyradius σ) (d : σ →₀ ℕ) : ℝ :=
  d.prod (fun i n => r i ^ n)

@[simp] theorem weight_zero {σ : Type u} (r : PositivePolyradius σ) :
    r.weight 0 = 1 := by simp [weight]

theorem weight_pos {σ : Type u} (r : PositivePolyradius σ) (d : σ →₀ ℕ) :
    0 < r.weight d := by
  exact Finset.prod_pos fun i _ => pow_pos (r.positive i) _

@[simp] theorem unit_weight {σ : Type u} (d : σ →₀ ℕ) :
    (unit σ).weight d = 1 := by simp [weight, Finsupp.prod]

end PositivePolyradius

variable {σ : Type u} (r : PositivePolyradius σ) (K : Type v)
  [NormedCommRing K] [IsUltrametricDist K]

/-- The actual subalgebra of weighted restricted formal power series. -/
def weightedRestrictedSubalgebra : Subalgebra K (MvPowerSeries σ K) where
  __ := MvPowerSeries.IsRestricted.subring r
  algebraMap_mem' a := MvPowerSeries.isRestricted_C r a

/-- The generalized Tate algebra with the displayed positive real polyradius. -/
def GeneralizedTateAlgebra := ↥(weightedRestrictedSubalgebra r K)

namespace GeneralizedTateAlgebra

instance : CommRing (GeneralizedTateAlgebra r K) :=
  inferInstanceAs (CommRing ↥(weightedRestrictedSubalgebra r K))

instance : Algebra K (GeneralizedTateAlgebra r K) :=
  inferInstanceAs (Algebra K ↥(weightedRestrictedSubalgebra r K))

instance [Nontrivial K] : Nontrivial (GeneralizedTateAlgebra r K) :=
  inferInstanceAs (Nontrivial ↥(weightedRestrictedSubalgebra r K))

/-- The underlying formal series; multiplication is its convolution. -/
def series (f : GeneralizedTateAlgebra r K) : MvPowerSeries σ K := f.val

theorem hasGaussNorm (f : GeneralizedTateAlgebra r K) :
    MvPowerSeries.HasGaussNorm norm r (series r K f) := by
  exact (Metric.isBounded_range_of_tendsto_cofinite f.property).bddAbove

/-- The weighted Gauss norm as an additive group norm. -/
def gaussAddGroupNorm : AddGroupNorm (GeneralizedTateAlgebra r K) where
  toFun f := MvPowerSeries.gaussNorm norm r (series r K f)
  map_zero' := MvPowerSeries.gaussNorm_zero norm r (norm_zero)
  add_le' f g := by
    apply (MvPowerSeries.gaussNorm_add_le_max norm r f.val g.val
      (fun i => (r.positive i).le) norm_nonneg
      IsUltrametricDist.norm_add_le_max (hasGaussNorm r K f) (hasGaussNorm r K g)).trans
    exact max_le_add_of_nonneg
      (MvPowerSeries.gaussNorm_nonneg norm r f.val norm_nonneg)
      (MvPowerSeries.gaussNorm_nonneg norm r g.val norm_nonneg)
  neg' f := MvPowerSeries.gaussNorm_neg norm r norm_neg f.val
  eq_zero_of_map_eq_zero' f hf := by
    apply Subtype.ext
    exact (MvPowerSeries.gaussNorm_eq_zero_iff norm r f.val norm_zero norm_nonneg
      (fun _ h => norm_eq_zero.mp h) r.positive (hasGaussNorm r K f)).mp hf

instance : NormedAddCommGroup (GeneralizedTateAlgebra r K) :=
  (gaussAddGroupNorm r K).toNormedAddCommGroup

/-- The norm is exactly the weighted supremum on the actual coefficients. -/
theorem norm_eq_gaussNorm (f : GeneralizedTateAlgebra r K) :
    ‖f‖ = MvPowerSeries.gaussNorm norm r (series r K f) := rfl

theorem weighted_norm_coeff_le (f : GeneralizedTateAlgebra r K) (d : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff d (series r K f)‖ * r.weight d ≤ ‖f‖ :=
  MvPowerSeries.le_gaussNorm norm r f.val (hasGaussNorm r K f) d

theorem norm_le_iff (f : GeneralizedTateAlgebra r K) {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ d, ‖MvPowerSeries.coeff d (series r K f)‖ * r.weight d ≤ C := by
  constructor
  · intro h d
    exact (weighted_norm_coeff_le r K f d).trans h
  · intro h
    exact Real.iSup_le h hC

instance : NormedCommRing (GeneralizedTateAlgebra r K) :=
  { (inferInstance : NormedAddCommGroup (GeneralizedTateAlgebra r K)),
    (inferInstance : CommRing (GeneralizedTateAlgebra r K)) with
    norm_mul_le := fun f g => MvPowerSeries.gaussNorm_mul_le norm r f.val g.val
      (fun i => (r.positive i).le) norm_nonneg norm_mul_le
      IsUltrametricDist.norm_add_le_max norm_zero (hasGaussNorm r K f) (hasGaussNorm r K g) }

instance : IsUltrametricDist (GeneralizedTateAlgebra r K) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g =>
    MvPowerSeries.gaussNorm_add_le_max norm r f.val g.val
      (fun i => (r.positive i).le) norm_nonneg
      IsUltrametricDist.norm_add_le_max (hasGaussNorm r K f) (hasGaussNorm r K g)

/-- A coefficient monomial is genuinely weighted restricted. -/
def monomial (d : σ →₀ ℕ) (a : K) : GeneralizedTateAlgebra r K :=
  ⟨MvPowerSeries.monomial d a, MvPowerSeries.isRestricted_monomial r d a⟩

@[simp] theorem coeff_monomial [DecidableEq σ] (d t : σ →₀ ℕ) (a : K) :
    MvPowerSeries.coeff t (series r K (monomial r K d a)) = if d = t then a else 0 := by
  classical
  simpa only [series, monomial, eq_comm] using MvPowerSeries.coeff_monomial t d a

/-- A monomial has its coefficient norm times its exact positive weight. -/
theorem norm_monomial (d : σ →₀ ℕ) (a : K) :
    ‖monomial r K d a‖ = ‖a‖ * r.weight d := by
  classical
  apply le_antisymm
  · apply (norm_le_iff r K _ (mul_nonneg (norm_nonneg a) (r.weight_pos d).le)).mpr
    intro t
    rw [coeff_monomial]
    split_ifs with h
    · subst t
      exact le_rfl
    · simp only [norm_zero, zero_mul]
      exact mul_nonneg (norm_nonneg a) (r.weight_pos d).le
  · simpa using weighted_norm_coeff_le r K (monomial r K d a) d

/-- The scalar inclusion preserves the given coefficient norm. -/
theorem norm_algebraMap (a : K) :
    ‖algebraMap K (GeneralizedTateAlgebra r K) a‖ = ‖a‖ := by
  have h : algebraMap K (GeneralizedTateAlgebra r K) a = monomial r K 0 a := by
    apply Subtype.ext
    exact (MvPowerSeries.monomial_zero_eq_C_apply a).symm
  rw [h, norm_monomial, PositivePolyradius.weight_zero, mul_one]

instance [NormOneClass K] : NormOneClass (GeneralizedTateAlgebra r K) where
  norm_one := by simpa using norm_algebraMap r K (1 : K)

/-- The radius-one identification keeps every formal coefficient unchanged. -/
def unitAlgEquiv : GeneralizedTateAlgebra (PositivePolyradius.unit σ) K ≃ₐ[K]
    StrictTateAlgebra σ K where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem norm_unitAlgEquiv (f : GeneralizedTateAlgebra (PositivePolyradius.unit σ) K) :
    ‖unitAlgEquiv K f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (StrictTateAlgebra.norm_le_iff σ K _ (norm_nonneg f)).mpr
    intro d
    change ‖MvPowerSeries.coeff d f.val‖ ≤ ‖f‖
    simpa only [series, PositivePolyradius.unit_weight, mul_one] using
      weighted_norm_coeff_le (PositivePolyradius.unit σ) K f d
  · apply (norm_le_iff (PositivePolyradius.unit σ) K _ (norm_nonneg _)).mpr
    intro d
    have h := StrictTateAlgebra.norm_coeff_le σ K (unitAlgEquiv K f) d
    change ‖MvPowerSeries.coeff d f.val‖ ≤ ‖unitAlgEquiv K f‖ at h
    simpa only [series, PositivePolyradius.unit_weight, mul_one] using h

theorem isometry_unitAlgEquiv : Isometry (unitAlgEquiv (σ := σ) K) := by
  apply AddMonoidHomClass.isometry_of_norm
  exact norm_unitAlgEquiv K

end GeneralizedTateAlgebra

namespace GeneralizedTateAlgebra

variable {σ : Type u} (r : PositivePolyradius σ) (K : Type v)
  [NormedField K] [IsUltrametricDist K]

instance : NormedAlgebra K (GeneralizedTateAlgebra r K) where
  norm_smul_le c f := by
    apply (norm_le_iff r K (c • f) (mul_nonneg (norm_nonneg c) (norm_nonneg f))).mpr
    intro d
    change ‖MvPowerSeries.coeff d (c • f.val)‖ * r.weight d ≤ _
    calc
      _ = ‖c‖ * (‖MvPowerSeries.coeff d f.val‖ * r.weight d) := by
        rw [MvPowerSeries.coeff_smul, norm_mul, mul_assoc]
      _ ≤ ‖c‖ * ‖f‖ := mul_le_mul_of_nonneg_left
        (weighted_norm_coeff_le r K f d) (norm_nonneg c)

end GeneralizedTateAlgebra

end Langlands.Analytic
