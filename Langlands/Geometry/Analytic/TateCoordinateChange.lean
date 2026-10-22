import Langlands.Geometry.Analytic.TateUniversal

/-! # Actual triangular coordinate changes on strict Tate algebras -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTateAlgebra

variable {σ : Type u} {K : Type v}
  [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An actual triangular coordinate tuple, with a chosen pivot coordinate. -/
def shearTuple (p : σ) (e : σ → ℕ) (c : σ → K) (i : σ) :
    StrictTateAlgebra σ K :=
  X σ K i + algebraMap K (StrictTateAlgebra σ K) (c i) * X σ K p ^ e i

omit [CompleteSpace K] in
theorem norm_shearTuple_le (p : σ) (e : σ → ℕ) (c : σ → K)
    (hc : ∀ i, ‖c i‖ ≤ 1) (i : σ) : ‖shearTuple p e c i‖ ≤ 1 := by
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · exact (norm_X σ K i).le
  · apply (norm_mul_le _ _).trans
    rw [norm_algebraMap]
    have hp : ‖X σ K p ^ e i‖ ≤ 1 :=
      (norm_pow_le _ _).trans (by rw [norm_X, one_pow])
    exact (mul_le_mul (hc i) hp (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- Evaluation at the triangular tuple is a genuine bounded algebra map. -/
def shearHom (p : σ) (e : σ → ℕ) (c : σ → K) (hc : ∀ i, ‖c i‖ ≤ 1) :
    BoundedAlgHom K (StrictTateAlgebra σ K) (StrictTateAlgebra σ K) :=
  evaluateHom σ K (StrictTateAlgebra σ K) (shearTuple p e c)
    (hasBoundedMonomials_of_norm_le σ _ _ (norm_shearTuple_le p e c hc))

@[simp]
theorem shearHom_X (p : σ) (e : σ → ℕ) (c : σ → K)
    (hc : ∀ i, ‖c i‖ ≤ 1) (i : σ) :
    shearHom p e c hc (X σ K i) = shearTuple p e c i :=
  evaluate_X σ K _ _ i

theorem shearHom_pivot (p : σ) (e : σ → ℕ) (c : σ → K)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hpc : c p = 0) :
    shearHom p e c hc (X σ K p) = X σ K p := by
  rw [shearHom_X, shearTuple, hpc, map_zero, zero_mul, add_zero]

theorem norm_shearHom_le (p : σ) (e : σ → ℕ) (c : σ → K)
    (hc : ∀ i, ‖c i‖ ≤ 1) (f : StrictTateAlgebra σ K) :
    ‖shearHom p e c hc f‖ ≤ ‖f‖ :=
  evaluate_norm_le σ K _ _ (norm_shearTuple_le p e c hc) f

/-- Opposite triangular coordinate changes cancel on the actual restricted
series algebra, by bounded-map uniqueness from their coordinate images. -/
theorem shearHom_comp_eq_id (p : σ) (e : σ → ℕ) (c d : σ → K)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hd : ∀ i, ‖d i‖ ≤ 1)
    (hpd : d p = 0) (hcd : ∀ i, d i + c i = 0) :
    BoundedAlgHom.comp (shearHom p e d hd) (shearHom p e c hc) =
      BoundedAlgHom.id K (StrictTateAlgebra σ K) := by
  apply hom_ext σ K (StrictTateAlgebra σ K)
  intro i
  change (shearHom p e d hd).toAlgHom (shearHom p e c hc (X σ K i)) = X σ K i
  rw [shearHom_X, shearTuple, map_add, map_mul, map_pow, AlgHom.commutes]
  change shearHom p e d hd (X σ K i) +
    algebraMap K (StrictTateAlgebra σ K) (c i) *
      shearHom p e d hd (X σ K p) ^ e i = X σ K i
  rw [shearHom_X, shearHom_pivot p e d hd hpd, shearTuple]
  calc
    X σ K i + algebraMap K (StrictTateAlgebra σ K) (d i) * X σ K p ^ e i +
        algebraMap K (StrictTateAlgebra σ K) (c i) * X σ K p ^ e i =
      X σ K i + algebraMap K (StrictTateAlgebra σ K) (d i + c i) *
        X σ K p ^ e i := by rw [map_add]; ring
    _ = X σ K i := by rw [hcd, map_zero, zero_mul, add_zero]

/-- The inverse is constructed by negating the coefficients. The pivot
coefficient is zero, so both substitutions leave the pivot fixed. -/
def coordinateShear (p : σ) (e : σ → ℕ) (c : σ → K)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hpc : c p = 0) :
    StrictTateAlgebra σ K ≃ₐ[K] StrictTateAlgebra σ K where
  __ := (shearHom p e c hc).toAlgHom
  invFun := shearHom p e (fun i => -c i) (fun i => by simpa using hc i)
  left_inv f := by
    have h := shearHom_comp_eq_id p e c (fun i => -c i) hc
      (fun i => by simpa using hc i) (by simp [hpc]) (fun i => neg_add_cancel (c i))
    exact congrArg (fun φ : BoundedAlgHom K (StrictTateAlgebra σ K)
      (StrictTateAlgebra σ K) => φ f) h
  right_inv f := by
    have h := shearHom_comp_eq_id p e (fun i => -c i) c
      (fun i => by simpa using hc i) hc hpc (fun i => add_neg_cancel (c i))
    exact congrArg (fun φ : BoundedAlgHom K (StrictTateAlgebra σ K)
      (StrictTateAlgebra σ K) => φ f) h

theorem coordinateShear_norm (p : σ) (e : σ → ℕ) (c : σ → K)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hpc : c p = 0) (f : StrictTateAlgebra σ K) :
    ‖coordinateShear p e c hc hpc f‖ = ‖f‖ := by
  apply le_antisymm (norm_shearHom_le p e c hc f)
  have h := norm_shearHom_le p e (fun i => -c i)
    (fun i => by simpa using hc i) (coordinateShear p e c hc hpc f)
  change ‖(coordinateShear p e c hc hpc).symm
    (coordinateShear p e c hc hpc f)‖ ≤ _ at h
  rw [AlgEquiv.symm_apply_apply] at h
  exact h

/-- Both the forward and inverse actual substitutions are contractive,
so the algebra automorphism is an isometry. -/
theorem coordinateShear_isometry (p : σ) (e : σ → ℕ) (c : σ → K)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hpc : c p = 0) :
    Isometry (coordinateShear p e c hc hpc) := by
  apply isometry_iff_dist_eq.mpr
  intro f g
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact coordinateShear_norm p e c hc hpc (f - g)

/-- The power substitutions used for analytic normalization. Only the
pivot coordinate is left unchanged. -/
def powerShear (p : σ) (e : σ → ℕ) :
    StrictTateAlgebra σ K ≃ₐ[K] StrictTateAlgebra σ K := by
  classical
  exact coordinateShear p e (fun i => if i = p then 0 else 1)
    (fun i => by split_ifs <;> simp) (by simp)

theorem powerShear_pivot (p : σ) (e : σ → ℕ) :
    powerShear (K := K) p e (X σ K p) = X σ K p := by
  classical
  exact shearHom_pivot p e (fun i => if i = p then 0 else 1)
    (fun i => by split_ifs <;> simp) (by simp)

theorem powerShear_other (p : σ) (e : σ → ℕ) (i : σ) (hi : i ≠ p) :
    powerShear (K := K) p e (X σ K i) = X σ K i + X σ K p ^ e i := by
  classical
  change shearHom p e (fun i => if i = p then 0 else 1)
    (fun i => by split_ifs <;> simp) (X σ K i) = _
  rw [shearHom_X, shearTuple]
  simp [hi]

theorem powerShear_isometry (p : σ) (e : σ → ℕ) :
    Isometry (powerShear (K := K) p e) := by
  classical
  exact coordinateShear_isometry p e _ _ _

end Langlands.Analytic.StrictTateAlgebra
