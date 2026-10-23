import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.EvaluationDefinitions
import Langlands.Geometry.Analytic.Affinoid
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Embedding

/-! # Isometric variable inclusions in weighted Tate algebras -/

noncomputable section

open Filter
open scoped Topology

universe u v w

namespace Langlands.Analytic

namespace PositivePolyradius

/-- Concatenate two finite positive polyradii without changing either block. -/
def append {n m : ℕ} (r : PositivePolyradius (Fin n))
    (s : PositivePolyradius (Fin m)) : PositivePolyradius (Fin (n + m)) where
  radius := Fin.addCases r s
  positive := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using r.positive j
    · simpa using s.positive j

@[simp] theorem append_castAdd {n m : ℕ} (r : PositivePolyradius (Fin n))
    (s : PositivePolyradius (Fin m)) (i : Fin n) :
    append r s (Fin.castAdd m i) = r i := by simp [append]

@[simp] theorem append_natAdd {n m : ℕ} (r : PositivePolyradius (Fin n))
    (s : PositivePolyradius (Fin m)) (i : Fin m) :
    append r s (Fin.natAdd n i) = s i := by simp [append]

/-- Preserving the variable radii preserves every monomial weight. -/
theorem weight_embDomain {σ : Type u} {τ : Type v}
    (r : PositivePolyradius σ) (s : PositivePolyradius τ) (e : σ ↪ τ)
    (he : ∀ i, s (e i) = r i) (d : σ →₀ ℕ) :
    s.weight (Finsupp.embDomain e d) = r.weight d := by
  simp only [weight, Finsupp.prod_embDomain, he]

end PositivePolyradius

namespace GeneralizedTateAlgebra

section GeneralCoefficients

variable {σ : Type u} {τ : Type v}
  (r : PositivePolyradius σ) (s : PositivePolyradius τ)
  (e : σ ↪ τ) (he : ∀ i, s (e i) = r i)
  (K : Type w) [NormedCommRing K] [IsUltrametricDist K]

include he in
/-- Formal variable inclusion preserves weighted restrictedness directly. -/
theorem isRestricted_rename (f : GeneralizedTateAlgebra r K) :
    MvPowerSeries.IsRestricted s (MvPowerSeries.rename e (series r K f)) := by
  classical
  change Tendsto (fun d => ‖MvPowerSeries.coeff d
    (MvPowerSeries.rename e (series r K f))‖ * s.weight d) cofinite (𝓝 0)
  have hf : Tendsto (fun d => ‖MvPowerSeries.coeff d (series r K f)‖ * r.weight d)
      cofinite (𝓝 0) := f.property
  rw [Metric.tendsto_nhds]
  intro ε hε
  apply eventually_cofinite.mpr
  apply ((eventually_cofinite.mp ((Metric.tendsto_nhds.mp hf) ε hε)).image
    (Finsupp.embDomain e)).subset
  intro d hd
  by_cases h : d ∈ Set.range (Finsupp.embDomain e)
  · obtain ⟨a, rfl⟩ := h
    refine ⟨a, ?_, rfl⟩
    simpa only [Set.mem_ofPred_eq, MvPowerSeries.coeff_embDomain_rename,
      PositivePolyradius.weight_embDomain r s e he] using hd
  · have hz : MvPowerSeries.coeff d (MvPowerSeries.rename e (series r K f)) = 0 :=
      MvPowerSeries.coeff_rename_eq_zero e _ (by
        rw [← funext (Finsupp.embDomain_eq_mapDomain e)]
        exact h)
    simp only [Set.mem_ofPred_eq, hz, norm_zero, zero_mul, dist_self, not_lt] at hd
    exact False.elim (not_le_of_gt hε hd)

/-- Include a series by formal renaming; no evaluation or completeness is needed. -/
def rename : GeneralizedTateAlgebra r K →ₐ[K] GeneralizedTateAlgebra s K where
  toFun f := ⟨MvPowerSeries.rename e (series r K f), isRestricted_rename r s e he K f⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.rename e))
  map_mul' f g := Subtype.ext (map_mul (MvPowerSeries.rename e) f.val g.val)
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.rename e))
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.rename e) f.val g.val)
  commutes' a := Subtype.ext ((MvPowerSeries.rename e).commutes a)

@[simp] theorem series_rename (f : GeneralizedTateAlgebra r K) :
    series s K (rename r s e he K f) = MvPowerSeries.rename e (series r K f) := rfl

@[simp] theorem coeff_embDomain_rename (f : GeneralizedTateAlgebra r K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain e d) (series s K (rename r s e he K f)) =
      MvPowerSeries.coeff d (series r K f) :=
  MvPowerSeries.coeff_embDomain_rename e _ d

/-- Renaming is exactly isometric for the weighted Gauss norms. -/
theorem norm_rename (f : GeneralizedTateAlgebra r K) :
    ‖rename r s e he K f‖ = ‖f‖ := by
  classical
  apply le_antisymm
  · apply (norm_le_iff s K _ (norm_nonneg f)).mpr
    intro d
    by_cases h : d ∈ Set.range (Finsupp.embDomain e)
    · obtain ⟨a, rfl⟩ := h
      rw [coeff_embDomain_rename, PositivePolyradius.weight_embDomain r s e he]
      exact weighted_norm_coeff_le r K f a
    · rw [series_rename, MvPowerSeries.coeff_rename_eq_zero e _ (by
        rw [← funext (Finsupp.embDomain_eq_mapDomain e)]
        exact h), norm_zero, zero_mul]
      exact norm_nonneg f
  · apply (norm_le_iff r K _ (norm_nonneg _)).mpr
    intro d
    have h := weighted_norm_coeff_le s K (rename r s e he K f) (Finsupp.embDomain e d)
    simpa only [coeff_embDomain_rename, PositivePolyradius.weight_embDomain r s e he] using h

theorem isometry_rename : Isometry (rename r s e he K) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_rename r s e he K)

@[simp] theorem rename_monomial (d : σ →₀ ℕ) (a : K) :
    rename r s e he K (monomial r K d a) =
      monomial s K (Finsupp.embDomain e d) a := by
  apply Subtype.ext
  exact (MvPowerSeries.rename_monomial e d a).trans
    (congrArg (fun t => MvPowerSeries.monomial t a) (Finsupp.embDomain_eq_mapDomain e d).symm)

@[simp] theorem rename_X (i : σ) :
    rename r s e he K (X r K i) = X s K (e i) := by
  simp [X, rename_monomial]

/-- Setting all variables outside the inclusion to zero is contractive. -/
def killCompl : GeneralizedTateAlgebra s K →ₐ[K] GeneralizedTateAlgebra r K where
  toFun f := ⟨MvPowerSeries.killCompl e (series s K f), by
    change Tendsto (fun d => ‖MvPowerSeries.coeff d
      (MvPowerSeries.killCompl e (series s K f))‖ * r.weight d) cofinite (𝓝 0)
    have hf : Tendsto (fun d => ‖MvPowerSeries.coeff d (series s K f)‖ * s.weight d)
        cofinite (𝓝 0) := f.property
    simpa only [Function.comp_def, MvPowerSeries.coeff_killCompl,
      PositivePolyradius.weight_embDomain r s e he] using
        hf.comp (Finsupp.embDomain_injective e).tendsto_cofinite⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.killCompl e))
  map_mul' f g := Subtype.ext (map_mul (MvPowerSeries.killCompl e) f.val g.val)
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.killCompl e))
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.killCompl e) f.val g.val)
  commutes' a := Subtype.ext ((MvPowerSeries.killCompl e).commutes a)

@[simp] theorem coeff_killCompl (f : GeneralizedTateAlgebra s K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (series r K (killCompl r s e he K f)) =
      MvPowerSeries.coeff (Finsupp.embDomain e d) (series s K f) := rfl

theorem norm_killCompl_le (f : GeneralizedTateAlgebra s K) :
    ‖killCompl r s e he K f‖ ≤ ‖f‖ := by
  apply (norm_le_iff r K _ (norm_nonneg f)).mpr
  intro d
  rw [coeff_killCompl, ← PositivePolyradius.weight_embDomain r s e he d]
  exact weighted_norm_coeff_le s K f _

@[simp] theorem killCompl_rename (f : GeneralizedTateAlgebra r K) :
    killCompl r s e he K (rename r s e he K f) = f := by
  apply Subtype.ext
  exact MvPowerSeries.killCompl_rename_app _

@[simp] theorem killCompl_X (i : σ) :
    killCompl r s e he K (X s K (e i)) = X r K i := by
  rw [← rename_X r s e he K, killCompl_rename]

@[simp] theorem killCompl_X_eq_zero {i : τ} (hi : i ∉ Set.range e) :
    killCompl r s e he K (X s K i) = 0 := by
  apply Subtype.ext
  exact MvPowerSeries.killCompl_X_eq_zero hi

end GeneralCoefficients

section BoundedMaps

variable {σ : Type u} {τ : Type v}
  (r : PositivePolyradius σ) (s : PositivePolyradius τ)
  (e : σ ↪ τ) (he : ∀ i, s (e i) = r i)
  (K : Type w) [NormedField K] [IsUltrametricDist K]

/-- The variable inclusion as a bounded algebra map, with bound one. -/
def boundedRename :
    BoundedAlgHom K (GeneralizedTateAlgebra r K) (GeneralizedTateAlgebra s K) where
  toAlgHom := rename r s e he K
  bounded := ⟨1, zero_lt_one, fun f => by simp [norm_rename]⟩

/-- The complementary-variable zero map as a bounded algebra map, with bound one. -/
def boundedKillCompl :
    BoundedAlgHom K (GeneralizedTateAlgebra s K) (GeneralizedTateAlgebra r K) where
  toAlgHom := killCompl r s e he K
  bounded := ⟨1, zero_lt_one, fun f => by
    change ‖killCompl r s e he K f‖ ≤ 1 * ‖f‖
    rw [one_mul]
    exact norm_killCompl_le r s e he K f⟩

@[simp] theorem boundedRename_apply (f : GeneralizedTateAlgebra r K) :
    boundedRename r s e he K f = rename r s e he K f := rfl

@[simp] theorem boundedKillCompl_apply (f : GeneralizedTateAlgebra s K) :
    boundedKillCompl r s e he K f = killCompl r s e he K f := rfl

@[simp] theorem boundedKillCompl_comp_boundedRename :
    (boundedKillCompl r s e he K).comp (boundedRename r s e he K) =
      BoundedAlgHom.id K (GeneralizedTateAlgebra r K) := by
  apply BoundedAlgHom.ext
  exact killCompl_rename r s e he K

end BoundedMaps

section FiniteAppend

variable {n m : ℕ} (r : PositivePolyradius (Fin n)) (s : PositivePolyradius (Fin m))
  (K : Type w) [NormedField K] [IsUltrametricDist K]

/-- Include the old variables in the first block of an enlarged polyradius. -/
def appendLeft : BoundedAlgHom K (GeneralizedTateAlgebra r K)
    (GeneralizedTateAlgebra (r.append s) K) :=
  boundedRename r (r.append s) (Fin.castAddEmb m)
    (fun i => PositivePolyradius.append_castAdd r s i) K

/-- Include the new variables in the second block of an enlarged polyradius. -/
def appendRight : BoundedAlgHom K (GeneralizedTateAlgebra s K)
    (GeneralizedTateAlgebra (r.append s) K) :=
  boundedRename s (r.append s) (Fin.natAddEmb n)
    (fun i => PositivePolyradius.append_natAdd r s i) K

/-- Retain the first block and set the second block to zero. -/
def appendProjectLeft : BoundedAlgHom K (GeneralizedTateAlgebra (r.append s) K)
    (GeneralizedTateAlgebra r K) :=
  boundedKillCompl r (r.append s) (Fin.castAddEmb m)
    (fun i => PositivePolyradius.append_castAdd r s i) K

/-- Retain the second block and set the first block to zero. -/
def appendProjectRight : BoundedAlgHom K (GeneralizedTateAlgebra (r.append s) K)
    (GeneralizedTateAlgebra s K) :=
  boundedKillCompl s (r.append s) (Fin.natAddEmb n)
    (fun i => PositivePolyradius.append_natAdd r s i) K

@[simp] theorem norm_appendLeft (f : GeneralizedTateAlgebra r K) :
    ‖appendLeft r s K f‖ = ‖f‖ :=
  norm_rename r (r.append s) (Fin.castAddEmb m)
    (fun i => PositivePolyradius.append_castAdd r s i) K f

@[simp] theorem norm_appendRight (f : GeneralizedTateAlgebra s K) :
    ‖appendRight r s K f‖ = ‖f‖ :=
  norm_rename s (r.append s) (Fin.natAddEmb n)
    (fun i => PositivePolyradius.append_natAdd r s i) K f

theorem norm_appendProjectLeft_le (f : GeneralizedTateAlgebra (r.append s) K) :
    ‖appendProjectLeft r s K f‖ ≤ ‖f‖ :=
  norm_killCompl_le r (r.append s) (Fin.castAddEmb m)
    (fun i => PositivePolyradius.append_castAdd r s i) K f

theorem norm_appendProjectRight_le (f : GeneralizedTateAlgebra (r.append s) K) :
    ‖appendProjectRight r s K f‖ ≤ ‖f‖ :=
  norm_killCompl_le s (r.append s) (Fin.natAddEmb n)
    (fun i => PositivePolyradius.append_natAdd r s i) K f

@[simp] theorem appendLeft_X (i : Fin n) :
    appendLeft r s K (X r K i) = X (r.append s) K (Fin.castAdd m i) :=
  rename_X r (r.append s) (Fin.castAddEmb m)
    (fun i => PositivePolyradius.append_castAdd r s i) K i

@[simp] theorem appendRight_X (i : Fin m) :
    appendRight r s K (X s K i) = X (r.append s) K (Fin.natAdd n i) :=
  rename_X s (r.append s) (Fin.natAddEmb n)
    (fun i => PositivePolyradius.append_natAdd r s i) K i

@[simp] theorem appendProjectLeft_appendLeft (f : GeneralizedTateAlgebra r K) :
    appendProjectLeft r s K (appendLeft r s K f) = f :=
  killCompl_rename r (r.append s) (Fin.castAddEmb m)
    (fun i => PositivePolyradius.append_castAdd r s i) K f

@[simp] theorem appendProjectRight_appendRight (f : GeneralizedTateAlgebra s K) :
    appendProjectRight r s K (appendRight r s K f) = f :=
  killCompl_rename s (r.append s) (Fin.natAddEmb n)
    (fun i => PositivePolyradius.append_natAdd r s i) K f

end FiniteAppend

end GeneralizedTateAlgebra

end Langlands.Analytic
