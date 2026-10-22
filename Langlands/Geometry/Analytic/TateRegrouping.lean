import Langlands.Geometry.Analytic.TateGaussPoint
import Langlands.Geometry.Analytic.TatePolynomial
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Regrouping actual restricted series by one variable -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTateAlgebra

open Filter
open scoped Topology

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]

omit [IsUltrametricDist A] in
private theorem cofinite_zero_iff {ι : Type*} (f : ι → A) :
    Tendsto f cofinite (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε → {i | ε ≤ ‖f i‖}.Finite := by
  rw [Metric.tendsto_nhds]
  simp only [dist_zero_right, Filter.eventually_cofinite, not_lt]

omit [IsUltrametricDist A] in
private theorem restricted_iff {σ : Type*} (f : MvPowerSeries σ A) :
    MvPowerSeries.IsRestricted (fun _ => (1 : ℝ)) f ↔
      Tendsto (fun i => MvPowerSeries.coeff i f) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [MvPowerSeries.IsRestricted, Finsupp.prod, one_pow,
    Finset.prod_const_one, mul_one]

/-- The actual coefficient slice under Mathlib's formal variable regrouping.
Restricted convergence follows along the injective exponent inclusion. -/
def slice {n : ℕ} (f : StrictTateAlgebra (Fin (n + 1)) A) (k : ℕ) :
    StrictTateAlgebra (Fin n) A :=
  ⟨PowerSeries.coeff k (MvPowerSeries.finSuccEquiv A n f.val), by
    apply restricted_iff _ |>.mpr
    have hi : Function.Injective (Finsupp.cons k : (Fin n →₀ ℕ) → (Fin (n + 1) →₀ ℕ)) :=
      fun x y h => (Finsupp.cons_injective2 h).2
    have ht := ((restricted_iff f.val).mp f.property).comp hi.tendsto_cofinite
    simpa only [Function.comp_def, MvPowerSeries.coeff_coeff_finSuccEquiv] using ht⟩

@[simp]
theorem coeff_slice {n : ℕ} (f : StrictTateAlgebra (Fin (n + 1)) A)
    (k : ℕ) (i : Fin n →₀ ℕ) :
    MvPowerSeries.coeff i (slice f k).val = MvPowerSeries.coeff (Finsupp.cons k i) f.val :=
  MvPowerSeries.coeff_coeff_finSuccEquiv f.val

theorem norm_slice_le {n : ℕ} (f : StrictTateAlgebra (Fin (n + 1)) A) (k : ℕ) :
    ‖slice f k‖ ≤ ‖f‖ := by
  apply (norm_le_iff (Fin n) A _ (norm_nonneg f)).mpr
  intro i
  change ‖MvPowerSeries.coeff i (slice f k).val‖ ≤ ‖f‖
  rw [coeff_slice]
  exact norm_coeff_le _ _ f _

/-- The slice norms tend to zero: each nonzero superlevel slice contains
an actual coefficient attaining that norm. -/
theorem slice_tendsto_zero {n : ℕ} (f : StrictTateAlgebra (Fin (n + 1)) A) :
    Tendsto (slice f) atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop, cofinite_zero_iff]
  intro ε hε
  have hs := (finite_coeff_norm_ge f hε).image (fun i => i 0)
  apply hs.subset
  intro k hk
  obtain ⟨i, hi⟩ := exists_norm_coeff_eq (slice f k)
  refine ⟨Finsupp.cons k i, ?_, Finsupp.cons_zero k i⟩
  change ε ≤ ‖MvPowerSeries.coeff (Finsupp.cons k i) f.val‖
  rw [← coeff_slice]
  change ε ≤ ‖MvPowerSeries.coeff i (series (Fin n) A (slice f k))‖
  rw [hi]
  exact hk

/-- Group by exponent of coordinate zero into actual one-variable restricted
series with coefficients in the smaller Tate algebra. -/
def regroup {n : ℕ} (f : StrictTateAlgebra (Fin (n + 1)) A) :
    RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A) :=
  ⟨PowerSeries.mk (slice f), by
    apply (PowerSeries.isRestricted_iff' 1 _).mpr
    simpa only [PowerSeries.coeff_mk, one_pow, mul_one] using
      (tendsto_zero_iff_norm_tendsto_zero.mp (slice_tendsto_zero f))⟩

@[simp]
theorem coeff_regroup {n : ℕ} (f : StrictTateAlgebra (Fin (n + 1)) A) (k : ℕ) :
    RestrictedSeries.coeff (StrictTateAlgebra (Fin n) A) k (regroup f) = slice f k := by
  change PowerSeries.coeff k (PowerSeries.mk (slice f)) = slice f k
  exact PowerSeries.coeff_mk k _

/-- Grouping coefficients preserves the actual Gauss norm. -/
theorem norm_regroup {n : ℕ} (f : StrictTateAlgebra (Fin (n + 1)) A) :
    ‖regroup f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (RestrictedSeries.norm_le_iff _ _ (norm_nonneg f)).mpr
    intro k
    rw [coeff_regroup]
    exact norm_slice_le f k
  · apply (norm_le_iff _ _ _ (norm_nonneg (regroup f))).mpr
    intro i
    calc
      ‖MvPowerSeries.coeff i (series _ _ f)‖ =
          ‖MvPowerSeries.coeff i.tail (slice f (i 0)).val‖ := by
        rw [coeff_slice, Finsupp.cons_tail]
        rfl
      _ ≤ ‖slice f (i 0)‖ := norm_coeff_le _ _ _ _
      _ ≤ ‖regroup f‖ := by
        rw [← coeff_regroup]
        exact (RestrictedSeries.norm_le_iff _ _ (norm_nonneg (regroup f))).mp le_rfl _

/-- Forget the two restrictedness proofs while retaining the actual
formal series. This is a genuine ring homomorphism. -/
def iteratedToFormal (n : ℕ) :
    RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A) →+*
      PowerSeries (MvPowerSeries (Fin n) A) :=
  (PowerSeries.map (restrictedSubalgebra (Fin n) A).val.toRingHom).comp
    (restrictedSubalgebra Unit (StrictTateAlgebra (Fin n) A)).val.toRingHom

@[simp]
theorem coeff_coeff_iteratedToFormal {n : ℕ}
    (f : RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A))
    (k : ℕ) (i : Fin n →₀ ℕ) :
    MvPowerSeries.coeff i (PowerSeries.coeff k (iteratedToFormal n f)) =
      MvPowerSeries.coeff i
        (RestrictedSeries.coeff (StrictTateAlgebra (Fin n) A) k f).val := rfl

theorem iteratedToFormal_injective (n : ℕ) :
    Function.Injective (iteratedToFormal (A := A) n) := by
  intro f g h
  apply Subtype.ext
  apply PowerSeries.ext
  intro k
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro i
  have ht := congrArg (fun s => MvPowerSeries.coeff i (PowerSeries.coeff k s)) h
  simpa only [coeff_coeff_iteratedToFormal, RestrictedSeries.coeff_apply] using ht

theorem iteratedToFormal_regroup {n : ℕ}
    (f : StrictTateAlgebra (Fin (n + 1)) A) :
    iteratedToFormal n (regroup f) = MvPowerSeries.finSuccEquiv A n f.val := by
  apply PowerSeries.ext
  intro k
  apply MvPowerSeries.ext
  intro i
  rw [coeff_coeff_iteratedToFormal, coeff_regroup, coeff_slice,
    MvPowerSeries.coeff_coeff_finSuccEquiv]

/-- Ungroup in the actual formal-series ring. Restrictedness is proved below. -/
def ungroupSeries {n : ℕ}
    (f : RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A)) :
    MvPowerSeries (Fin (n + 1)) A :=
  (MvPowerSeries.finSuccEquiv A n).symm (iteratedToFormal n f)

theorem coeff_ungroupSeries {n : ℕ}
    (f : RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A))
    (k : ℕ) (i : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.cons k i) (ungroupSeries f) =
      MvPowerSeries.coeff i
        (RestrictedSeries.coeff (StrictTateAlgebra (Fin n) A) k f).val := by
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp only [ungroupSeries, AlgEquiv.apply_symm_apply, coeff_coeff_iteratedToFormal]

/-- Restrictedness in the converse direction follows from a finite union of
finite coefficient superlevel sets in the finitely many large slices. -/
theorem ungroupSeries_restricted {n : ℕ}
    (f : RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A)) :
    MvPowerSeries.IsRestricted (fun _ => (1 : ℝ)) (ungroupSeries f) := by
  apply (restricted_iff _).mpr
  apply (cofinite_zero_iff _).mpr
  intro ε hε
  let c : ℕ → StrictTateAlgebra (Fin n) A :=
    fun k => RestrictedSeries.coeff (StrictTateAlgebra (Fin n) A) k f
  let S : Set ℕ := {k | ε ≤ ‖c k‖}
  let T : ℕ → Set (Fin n →₀ ℕ) :=
    fun k => {i | ε ≤ ‖MvPowerSeries.coeff i (c k).val‖}
  have hs : S.Finite := by
    have ht : Tendsto c cofinite (𝓝 0) := by
      rw [Nat.cofinite_eq_atTop]
      exact RestrictedSeries.coeff_tendsto_zero _ f
    exact (cofinite_zero_iff c).mp ht ε hε
  have ht (k : ℕ) : (T k).Finite := finite_coeff_norm_ge (c k) hε
  have hU : (⋃ k ∈ S, Finsupp.cons k '' T k).Finite :=
    hs.biUnion fun k _ => (ht k).image (Finsupp.cons k)
  apply hU.subset
  intro i hi
  have hi' : ε ≤ ‖MvPowerSeries.coeff i.tail (c (i 0)).val‖ := by
    change ε ≤ ‖MvPowerSeries.coeff i.tail
      (RestrictedSeries.coeff (StrictTateAlgebra (Fin n) A) (i 0) f).val‖
    rw [← coeff_ungroupSeries, Finsupp.cons_tail]
    exact hi
  have hk : i 0 ∈ S := hi'.trans (norm_coeff_le _ _ _ _)
  exact Set.mem_iUnion.mpr ⟨i 0, Set.mem_iUnion.mpr
    ⟨hk, ⟨i.tail, hi', Finsupp.cons_tail i⟩⟩⟩

/-- The genuine converse restricted-series construction. -/
def ungroup {n : ℕ}
    (f : RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A)) :
    StrictTateAlgebra (Fin (n + 1)) A :=
  ⟨ungroupSeries f, ungroupSeries_restricted f⟩

@[simp]
theorem ungroup_regroup {n : ℕ}
    (f : StrictTateAlgebra (Fin (n + 1)) A) : ungroup (regroup f) = f := by
  apply Subtype.ext
  change (MvPowerSeries.finSuccEquiv A n).symm (iteratedToFormal n (regroup f)) = f.val
  rw [iteratedToFormal_regroup, AlgEquiv.symm_apply_apply]

@[simp]
theorem regroup_ungroup {n : ℕ}
    (f : RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A)) :
    regroup (ungroup f) = f := by
  apply iteratedToFormal_injective n
  rw [iteratedToFormal_regroup]
  exact (MvPowerSeries.finSuccEquiv A n).apply_symm_apply _

/-- Actual finite-variable Tate algebras regroup as one-variable restricted
series over the smaller actual Tate algebra. -/
def regroupEquiv (n : ℕ) :
    StrictTateAlgebra (Fin (n + 1)) A ≃+*
      RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A) where
  toFun := regroup
  invFun := ungroup
  left_inv := ungroup_regroup
  right_inv := regroup_ungroup
  map_add' f g := by
    apply iteratedToFormal_injective n
    rw [map_add, iteratedToFormal_regroup, iteratedToFormal_regroup,
      iteratedToFormal_regroup]
    exact (MvPowerSeries.finSuccEquiv A n).map_add f.val g.val
  map_mul' f g := by
    apply iteratedToFormal_injective n
    rw [map_mul, iteratedToFormal_regroup, iteratedToFormal_regroup,
      iteratedToFormal_regroup]
    exact (MvPowerSeries.finSuccEquiv A n).map_mul f.val g.val

/-- The constructed ring equivalence is an isometry for the Gauss norms. -/
theorem regroupEquiv_isometry (n : ℕ) : Isometry (regroupEquiv (A := A) n) := by
  apply isometry_iff_dist_eq.mpr
  intro f g
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact norm_regroup (f - g)

/-- Regrouping sends a scalar to the same scalar through the two actual
constant-series maps. -/
theorem regroup_algebraMap (n : ℕ) (a : A) :
    regroup (algebraMap A (StrictTateAlgebra (Fin (n + 1)) A) a) =
      algebraMap (StrictTateAlgebra (Fin n) A)
        (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) A))
        (algebraMap A (StrictTateAlgebra (Fin n) A) a) := by
  apply iteratedToFormal_injective n
  rw [iteratedToFormal_regroup]
  change MvPowerSeries.finSuccEquiv A n (MvPowerSeries.C a) =
    PowerSeries.map (restrictedSubalgebra (Fin n) A).val.toRingHom
      (PowerSeries.C (algebraMap A (StrictTateAlgebra (Fin n) A) a))
  rw [MvPowerSeries.finSuccEquiv_C]
  exact (PowerSeries.map_C
    (restrictedSubalgebra (Fin n) A).val.toRingHom
    (algebraMap A (StrictTateAlgebra (Fin n) A) a)).symm

end Langlands.Analytic.StrictTateAlgebra
