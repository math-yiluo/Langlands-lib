import Langlands.Global.PrimitiveAdelicHeight

/-! # An actual content idele of a primitive adelic vector -/

noncomputable section

universe u

open scoped NNReal Topology Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

private theorem exists_coordinate_norm {K : Type*} [NormedField K]
    (z : Fin n → K) (hz : 0 < ‖z‖) : ∃ i, ‖z i‖ = ‖z‖ := by
  classical
  obtain ⟨j, _⟩ := Function.ne_iff.mp (norm_pos_iff.mp hz)
  let : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖)
    Finset.univ_nonempty
  refine ⟨i, le_antisymm (norm_le_pi_norm z i) ?_⟩
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => hi j (Finset.mem_univ j)

/-- A chosen nonzero coordinate attaining the maximum norm of a local vector. -/
def localContentUnit {K : Type*} [NormedField K]
    (z : Fin n → K) (hz : 0 < ‖z‖) : Kˣ :=
  Units.mk0 (z (exists_coordinate_norm n z hz).choose) (by
    apply norm_ne_zero_iff.mp
    rw [(exists_coordinate_norm n z hz).choose_spec]
    exact hz.ne')

@[simp] theorem norm_localContentUnit {K : Type*} [NormedField K]
    (z : Fin n → K) (hz : 0 < ‖z‖) :
    ‖(localContentUnit n z hz : K)‖ = ‖z‖ :=
  (exists_coordinate_norm n z hz).choose_spec

/-- The local content units at finite places of an actual primitive vector. -/
def finiteContentUnit (x : Vector F n) (hx : IsPrimitive F n x) (v : FinitePlace F) :
    (FiniteCompletion F v)ˣ :=
  localContentUnit n (fun i => finiteProjection F v (x i)) (hx.finiteNorm_pos F n v)

@[simp] theorem norm_finiteContentUnit (x : Vector F n) (hx : IsPrimitive F n x)
    (v : FinitePlace F) :
    ‖(finiteContentUnit F n x hx v : FiniteCompletion F v)‖ = finiteNorm F n x v :=
  norm_localContentUnit n _ _

/-- The local content units at infinite places of an actual primitive vector. -/
def infiniteContentUnit (x : Vector F n) (hx : IsPrimitive F n x) (v : InfinitePlace F) :
    (InfiniteCompletion F v)ˣ :=
  localContentUnit n (fun i => infiniteProjection F v (x i)) (hx.infiniteNorm_pos F n v)

@[simp] theorem norm_infiniteContentUnit (x : Vector F n) (hx : IsPrimitive F n x)
    (v : InfinitePlace F) :
    ‖(infiniteContentUnit F n x hx v : InfiniteCompletion F v)‖ = infiniteNorm F n x v :=
  norm_localContentUnit n _ _

private theorem eventually_finiteContentUnit_integral (x : Vector F n)
    (hx : IsPrimitive F n x) :
    ∀ᶠ v : FinitePlace F in Filter.cofinite,
      finiteContentUnit F n x hx v ∈ (v.adicCompletionIntegers F).units := by
  filter_upwards [hx.eventually_finiteNorm_eq_one F n] with v hv
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
  apply Valued.toNormedField.norm_eq_one_iff.mp
  rw [norm_finiteContentUnit, hv]

/-- The actual finite content idele, assembled using the finite-support result. -/
def finiteContent (x : Vector F n) (hx : IsPrimitive F n x) : FiniteIdeles F :=
  RestrictedProduct.mkUnit (B := fun v : FinitePlace F => v.adicCompletionIntegers F)
    (finiteContentUnit F n x hx) (eventually_finiteContentUnit_integral F n x hx)

/-- The actual archimedean content idele. -/
def infiniteContent (x : Vector F n) (hx : IsPrimitive F n x) : (InfiniteAdeles F)ˣ :=
  MulEquiv.piUnits.symm (infiniteContentUnit F n x hx)

/-- An actual content idele whose local norms are the maximum coordinate norms
of the primitive vector. No continuity of this chosen map is asserted. -/
def contentIdele (x : Vector F n) (hx : IsPrimitive F n x) : Ideles F :=
  (ideleProductEquiv F).symm (infiniteContent F n x hx, finiteContent F n x hx)

@[simp] theorem norm_contentIdele_finite (x : Vector F n) (hx : IsPrimitive F n x)
    (v : FinitePlace F) :
    ‖(contentIdele F n x hx).val.2 v‖ = finiteNorm F n x v :=
  norm_finiteContentUnit F n x hx v

@[simp] theorem norm_contentIdele_infinite (x : Vector F n) (hx : IsPrimitive F n x)
    (v : InfinitePlace F) :
    ‖(contentIdele F n x hx).val.1 v‖ = infiniteNorm F n x v :=
  norm_infiniteContentUnit F n x hx v

/-- The normalized idelic norm of the content idele is exactly the positive height. -/
theorem full_contentIdele (x : Vector F n) (hx : IsPrimitive F n x) :
    IdeleAbsoluteValue.full F (contentIdele F n x hx) = positiveHeight F n x hx := by
  apply Units.ext
  apply NNReal.eq
  simp only [IdeleAbsoluteValue.coe_full, norm_contentIdele_infinite,
    norm_contentIdele_finite, positiveHeight_val, height]

/-- Primitivity is preserved by actual invertible adelic matrices. -/
theorem IsPrimitive.mulVec {x : Vector F n} (hx : IsPrimitive F n x) (g : AdelicGL F n) :
    IsPrimitive F n (g.val *ᵥ x) := by
  obtain ⟨h, v, hv, rfl⟩ := hx
  refine ⟨g * h, v, hv, ?_⟩
  rw [Units.val_mul, Matrix.mulVec_mulVec]

/-- Primitivity is preserved by actual scalar ideles. -/
theorem IsPrimitive.smul {x : Vector F n} (hx : IsPrimitive F n x) (t : Ideles F) :
    IsPrimitive F n (t.val • x) := by
  have h := hx.mulVec F n (AdelicGL.scalar F n t)
  change IsPrimitive F n (Matrix.scalar (Fin n) t.val *ᵥ x) at h
  rwa [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h

/-- Divide a primitive vector by its chosen actual content idele. -/
def normalizedVector (x : Vector F n) (hx : IsPrimitive F n x) : Vector F n :=
  (contentIdele F n x hx)⁻¹.val • x

/-- The normalized vector remains primitive. -/
theorem normalizedVector_isPrimitive (x : Vector F n) (hx : IsPrimitive F n x) :
    IsPrimitive F n (normalizedVector F n x hx) :=
  hx.smul F n (contentIdele F n x hx)⁻¹

/-- The normalized vector has finite local maximum coordinate norm one. -/
@[simp] theorem finiteNorm_normalizedVector (x : Vector F n) (hx : IsPrimitive F n x)
    (v : FinitePlace F) : finiteNorm F n (normalizedVector F n x hx) v = 1 := by
  rw [normalizedVector, finiteNorm_smul]
  change ‖((finiteContentUnit F n x hx v : FiniteCompletion F v)⁻¹)‖ *
    finiteNorm F n x v = 1
  rw [norm_inv, norm_finiteContentUnit, inv_mul_cancel₀ (hx.finiteNorm_pos F n v).ne']

/-- The normalized vector has infinite local maximum coordinate norm one. -/
@[simp] theorem infiniteNorm_normalizedVector (x : Vector F n) (hx : IsPrimitive F n x)
    (v : InfinitePlace F) : infiniteNorm F n (normalizedVector F n x hx) v = 1 := by
  rw [normalizedVector, infiniteNorm_smul]
  change ‖((infiniteContentUnit F n x hx v : InfiniteCompletion F v)⁻¹)‖ *
    infiniteNorm F n x v = 1
  rw [norm_inv, norm_infiniteContentUnit, inv_mul_cancel₀ (hx.infiniteNorm_pos F n v).ne']

/-- The actual content idele recovers the original vector from its normalization. -/
theorem contentIdele_smul_normalizedVector (x : Vector F n) (hx : IsPrimitive F n x) :
    (contentIdele F n x hx).val • normalizedVector F n x hx = x := by
  rw [normalizedVector, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end Langlands.Global.PrimitiveAdelicHeight
