import Langlands.Representation.Archimedean.RealInterlacedJacquet

/-!
# Column functions and their expansions

Complex column combinations `X ↦ (X u)_i` of real matrices, the Plücker coordinates of two of
them on `4 × 4` matrices with their self-dual combinations `w₁, w₂, w₃`, and the expansions of
these functions along the block rotations.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealInterlacedJacquet

open Langlands.LocalFactor.Archimedean
open RealJacquetFrobenius RealBlockJacquet RealBlockMultiplier RealBlockRotation
  RealBlockFourierFinite RealBlockDerivative RealCharacterCrossing RealBlockFlatJacquet InductionStages

variable {n : ℕ}

/-! ## Column combinations -/

section Columns

/-- The complex column combination `X ↦ (X u)_i = Σ_c X_{ic} u_c`. -/
def colv (u : Fin n → ℂ) (i : Fin n) : MF n := fun X => ∑ c, ((X i c : ℝ) : ℂ) * u c

theorem colv_one (u : Fin n → ℂ) (i : Fin n) : colv u i 1 = u i := by
  simp only [colv]
  rw [Finset.sum_eq_single i (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
  simp

variable {b : ℕ}

theorem colv_rot_ia (hb : b + 1 < n) (u : Fin n → ℂ) (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    colv u (ia hb) ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * X) =
      (Real.cos t : ℂ) * colv u (ia hb) X - (Real.sin t : ℂ) * colv u (ib hb) X := by
  simp only [colv, rot_mul_ia, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  push_cast
  ring

theorem colv_rot_ib (hb : b + 1 < n) (u : Fin n → ℂ) (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    colv u (ib hb) ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * X) =
      (Real.sin t : ℂ) * colv u (ia hb) X + (Real.cos t : ℂ) * colv u (ib hb) X := by
  simp only [colv, rot_mul_ib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  push_cast
  ring

theorem colv_rot_of_ne (hb : b + 1 < n) (u : Fin n → ℂ) (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    {i : Fin n} (h1 : i ≠ ia hb) (h2 : i ≠ ib hb) :
    colv u i ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * X) = colv u i X := by
  simp only [colv, rot_mul_of_ne hb t X h1 h2]

theorem colv_diag (u : Fin n → ℂ) (i : Fin n) (s : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    colv u i (Matrix.diagonal s * X) = (s i : ℂ) * colv u i X := by
  simp only [colv, Matrix.diagonal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  push_cast
  ring

/-- The complex coordinate `y_b + i y_{b+1}` of the column `y = X u` at the block `b`. -/
def yZ (hb : b + 1 < n) (u : Fin n → ℂ) : MF n :=
  fun X => colv u (ia hb) X + Complex.I * colv u (ib hb) X

/-- The conjugate coordinate `y_b - i y_{b+1}`. -/
def yZb (hb : b + 1 < n) (u : Fin n → ℂ) : MF n :=
  fun X => colv u (ia hb) X - Complex.I * colv u (ib hb) X

theorem yZ_rot (hb : b + 1 < n) (u : Fin n → ℂ) (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    yZ hb u ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * X) =
      expMode 1 t * yZ hb u X := by
  simp only [yZ, colv_rot_ia, colv_rot_ib, expMode_one_eq]
  linear_combination (-(Real.sin t : ℂ) * colv u (ib hb) X) * Complex.I_sq

theorem yZb_rot (hb : b + 1 < n) (u : Fin n → ℂ) (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    yZb hb u ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * X) =
      expMode (-1) t * yZb hb u X := by
  simp only [yZb, colv_rot_ia, colv_rot_ib, expMode_neg_one_eq]
  linear_combination (-(Real.sin t : ℂ) * colv u (ib hb) X) * Complex.I_sq

theorem yZ_rot_of_disjoint (hb : b + 1 < n) {b' : ℕ} (hb' : b' + 1 < n)
    (hd : b + 1 < b' ∨ b' + 1 < b) (u : Fin n → ℂ) (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    yZ hb u ((blockRotation n b' t : Matrix (Fin n) (Fin n) ℝ) * X) = yZ hb u X := by
  have h1 : ia hb ≠ ia hb' := fun h => by simp [ia, Fin.ext_iff] at h; omega
  have h2 : ia hb ≠ ib hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h3 : ib hb ≠ ia hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h4 : ib hb ≠ ib hb' := fun h => by simp [ib, Fin.ext_iff] at h; omega
  simp only [yZ, colv_rot_of_ne hb' u t X h1 h2, colv_rot_of_ne hb' u t X h3 h4]

theorem yZb_rot_of_disjoint (hb : b + 1 < n) {b' : ℕ} (hb' : b' + 1 < n)
    (hd : b + 1 < b' ∨ b' + 1 < b) (u : Fin n → ℂ) (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    yZb hb u ((blockRotation n b' t : Matrix (Fin n) (Fin n) ℝ) * X) = yZb hb u X := by
  have h1 : ia hb ≠ ia hb' := fun h => by simp [ia, Fin.ext_iff] at h; omega
  have h2 : ia hb ≠ ib hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h3 : ib hb ≠ ia hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h4 : ib hb ≠ ib hb' := fun h => by simp [ib, Fin.ext_iff] at h; omega
  simp only [yZb, colv_rot_of_ne hb' u t X h1 h2, colv_rot_of_ne hb' u t X h3 h4]

end Columns

/-! ## Continuous `O(n)`-finite functions -/

section Finite

open TranslateFinite

/-- The algebra of continuous functions on matrices whose restrictions to `O(n)` are
`O(n)`-finite. -/
def PF (n : ℕ) : Subalgebra ℂ (MF n) where
  carrier := {H | Continuous H ∧
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => H (κ : Matrix (Fin n) (Fin n) ℝ))}
  mul_mem' := fun ha hb => ⟨ha.1.mul hb.1, isTranslateFinite_mul ha.2 hb.2⟩
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, isTranslateFinite_add ha.2 hb.2⟩
  algebraMap_mem' := fun c => ⟨continuous_const, by
    simpa using isTranslateFinite_const
      (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ) c⟩

theorem entry_mem_PF (i c : Fin n) :
    (fun X : Matrix (Fin n) (Fin n) ℝ => ((X i c : ℝ) : ℂ)) ∈ PF n :=
  ⟨continuous_entry i c, isTranslateFinite_entry (i, c)⟩

theorem colv_mem_PF (u : Fin n → ℂ) (i : Fin n) : colv u i ∈ PF n := by
  have e : colv u i = ∑ c, u c • (fun X : Matrix (Fin n) (Fin n) ℝ => ((X i c : ℝ) : ℂ)) := by
    funext X
    simp [colv, Finset.sum_apply, mul_comm]
  rw [e]
  exact Subalgebra.sum_mem _ fun c _ => Subalgebra.smul_mem _ (entry_mem_PF i c) _

theorem det_mem_PF : (fun X : Matrix (Fin n) (Fin n) ℝ => ((X.det : ℝ) : ℂ)) ∈ PF n := by
  refine ⟨Complex.continuous_ofReal.comp continuous_id.matrix_det, ?_⟩
  unfold IsTranslateFinite
  set d : Matrix.unitaryGroup (Fin n) ℝ → ℂ :=
    fun κ => (((κ : Matrix (Fin n) (Fin n) ℝ).det : ℝ) : ℂ) with hd
  have : FiniteDimensional ℂ (Submodule.span ℂ ({d} : Set (Matrix.unitaryGroup (Fin n) ℝ → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)
  suffices hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      Whittaker.rightTranslation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (id k) d) ≤
      Submodule.span ℂ {d} from Submodule.finiteDimensional_of_le hle
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine Submodule.mem_span_singleton.mpr ⟨(((k : Matrix (Fin n) (Fin n) ℝ).det : ℝ) : ℂ), ?_⟩
  funext κ
  show (((k : Matrix (Fin n) (Fin n) ℝ).det : ℝ) : ℂ) *
      (((κ : Matrix (Fin n) (Fin n) ℝ).det : ℝ) : ℂ) =
    ((((κ * k : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ).det : ℝ) : ℂ)
  rw [show ((κ * k : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
    (κ : Matrix (Fin n) (Fin n) ℝ) * (k : Matrix (Fin n) (Fin n) ℝ) from rfl, Matrix.det_mul]
  push_cast
  ring

theorem comp_left_mem_PF (m : Matrix.unitaryGroup (Fin n) ℝ) {H : MF n} (hH : H ∈ PF n) :
    (fun X => H ((m : Matrix (Fin n) (Fin n) ℝ) * X)) ∈ PF n := by
  refine ⟨hH.1.comp (continuous_const.matrix_mul continuous_id), ?_⟩
  have h := hH.2
  unfold IsTranslateFinite at h ⊢
  set L : (Matrix.unitaryGroup (Fin n) ℝ → ℂ) →ₗ[ℂ] (Matrix.unitaryGroup (Fin n) ℝ → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun κ => m * κ) with hL
  have e : Submodule.span ℂ (Set.range fun k =>
      Whittaker.rightTranslation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (id k)
        (fun κ : Matrix.unitaryGroup (Fin n) ℝ =>
          H ((m : Matrix (Fin n) (Fin n) ℝ) * (κ : Matrix (Fin n) (Fin n) ℝ)))) =
      (Submodule.span ℂ (Set.range fun k =>
        Whittaker.rightTranslation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (id k)
          (fun κ : Matrix.unitaryGroup (Fin n) ℝ => H (κ : Matrix (Fin n) (Fin n) ℝ)))).map L := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext k
    funext κ
    show H ((m : Matrix (Fin n) (Fin n) ℝ) *
        ((κ * k : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) =
      H (((m * κ) * k : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
    rw [mul_assoc]
    rfl
  rw [e]
  infer_instance

end Finite

/-! ## The special orthogonal group -/

section Special

/-- `SO(n)` inside `GL_n(ℝ)`. -/
def SOset (n : ℕ) : Set (Langlands.GeneralLinear n ℝ) :=
  {g | g ∈ unitaryCompact ℝ n ∧ (g : Matrix (Fin n) (Fin n) ℝ).det = 1}

theorem det_sq_of_mem {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    (g : Matrix (Fin n) (Fin n) ℝ).det * (g : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
  have h := (Matrix.det_of_mem_unitary hg).1
  simpa using h

theorem det_blockRotation (b : ℕ) (t : ℝ) :
    (blockRotation n b t : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
  have e : blockRotation n b t = blockRotation n b (t / 2) * blockRotation n b (t / 2) := by
    rw [← blockRotation_add]
    ring_nf
  rw [e, Units.val_mul, Matrix.det_mul]
  exact det_sq_of_mem (blockRotation_mem_unitaryCompact n b (t / 2))

theorem rot_mul_mem_SOset {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ SOset n) (b : ℕ) (t : ℝ) :
    blockRotation n b t * g ∈ SOset n :=
  ⟨(unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n b t) hg.1, by
    rw [Units.val_mul, Matrix.det_mul, det_blockRotation, hg.2, one_mul]⟩

theorem one_mem_SOset : (1 : Langlands.GeneralLinear n ℝ) ∈ SOset n :=
  ⟨one_mem _, by simp⟩

theorem blockRotation_mem_SOset (b : ℕ) (t : ℝ) : blockRotation n b t ∈ SOset n := by
  simpa using rot_mul_mem_SOset one_mem_SOset b t

end Special

/-! ## Steps of multipliers on `SO(n)` -/

section Steps

/-- **Fourier inversion along an expansion.** If `f` agrees with `H` along the orbit `r_b(t) κ`
and all block Fourier coefficients of `f` at `κ` vanish, then `f(κ) = 0`. -/
theorem eq_zero_of_modes {b N : ℕ} {H : MF n} {P : Polynomial (MF n)} (h : IsExpansion b N H P)
    {f : Langlands.GeneralLinear n ℝ → ℂ} {κ : Langlands.GeneralLinear n ℝ}
    (hf : ∀ t : ℝ, f (blockRotation n b t * κ) =
      H ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * (κ : Matrix (Fin n) (Fin n) ℝ)))
    (h0 : ∀ j : ℤ, blockFourierCoefficient n b j f κ = 0) : f κ = 0 := by
  have hc : ∀ k ∈ Finset.range (2 * N + 1), P.coeff k (κ : Matrix (Fin n) (Fin n) ℝ) = 0 := by
    intro k hk
    have h1 := blockFourierCoefficient_of_expansion h hf ((k : ℤ) - N)
    rw [h0, sum_ite_mode N _ _ (by omega) (by rw [Finset.mem_range] at hk; omega)] at h1
    have h2 : ((k : ℤ) - N + N).toNat = k := by omega
    rw [h2] at h1
    have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    exact (mul_eq_zero.mp h1.symm).resolve_left hπ
  have h1 := hf 0
  rw [h.apply, blockRotation_zero, one_mul] at h1
  rw [h1]
  exact Finset.sum_eq_zero fun k hk => by rw [hc k hk, zero_mul]

/-- **One step of a multiplier.** If `f = H` on `SO(n)` with `H ∈ S` and `S` is closed under
expansion along `b`, then `(2π)⁻¹ Σᶠ_j μ_j Φ_j(f)` agrees on `SO(n)` with some `H' ∈ S`. -/
theorem exists_step {b N : ℕ} {S T : Submodule ℂ (MF n)} (hS : HasExpTop b N S T) {H : MF n}
    (hH : H ∈ S) {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ∀ κ ∈ SOset n, f κ = H (κ : Matrix (Fin n) (Fin n) ℝ)) (μ : ℤ → ℂ) :
    ∃ H' ∈ S, ∀ κ ∈ SOset n, (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ j : ℤ, μ j *
      blockFourierCoefficient n b j f κ = H' (κ : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨P, hP, hPS, -⟩ := hS H hH
  refine ⟨∑ k ∈ Finset.range (2 * N + 1), μ ((k : ℤ) - N) • P.coeff k,
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hPS k), fun κ hκ => ?_⟩
  rw [finsum_of_expansion hP (fun t => by rw [hf _ (rot_mul_mem_SOset hκ b t)]; rfl) μ]
  simp [Finset.sum_apply]

/-- The block Fourier coefficients of a function agreeing with `H` on `SO(n)`, from an
expansion of `H`. -/
theorem blockFourierCoefficient_eq_of_expansion {b N : ℕ} {H : MF n} {P : Polynomial (MF n)}
    (h : IsExpansion b N H P) {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ∀ κ ∈ SOset n, f κ = H (κ : Matrix (Fin n) (Fin n) ℝ))
    {κ : Langlands.GeneralLinear n ℝ} (hκ : κ ∈ SOset n) (j : ℤ) :
    blockFourierCoefficient n b j f κ = if 0 ≤ j + N ∧ j + N ≤ 2 * N then
      2 * (Real.pi : ℂ) * P.coeff (j + N).toNat (κ : Matrix (Fin n) (Fin n) ℝ) else 0 := by
  rw [blockFourierCoefficient_of_expansion h
    (fun t => by rw [hf _ (rot_mul_mem_SOset hκ b t)]; rfl) j]
  split_ifs with hj
  · exact sum_ite_mode N _ _ hj.1 (by omega)
  · exact sum_ite_mode_eq_zero N _ _ (by omega)

end Steps

/-! ## Spans of column functions -/

section Spans

variable {b : ℕ}

/-- The span of the column functions `X ↦ (X u)_i`. -/
def Ly (u : Fin n → ℂ) : Submodule ℂ (MF n) := Submodule.span ℂ (Set.range fun i => colv u i)

theorem colv_mem_Ly (u : Fin n → ℂ) (i : Fin n) : colv u i ∈ Ly u :=
  Submodule.subset_span ⟨i, rfl⟩

theorem yZ_mem_Ly (hb : b + 1 < n) (u : Fin n → ℂ) : yZ hb u ∈ Ly u := by
  have e : yZ hb u = colv u (ia hb) + Complex.I • colv u (ib hb) := by
    funext X
    simp [yZ]
  rw [e]
  exact Submodule.add_mem _ (colv_mem_Ly u _) (Submodule.smul_mem _ _ (colv_mem_Ly u _))

theorem yZb_mem_Ly (hb : b + 1 < n) (u : Fin n → ℂ) : yZb hb u ∈ Ly u := by
  have e : yZb hb u = colv u (ia hb) + (-Complex.I) • colv u (ib hb) := by
    funext X
    simp [yZb, sub_eq_add_neg]
  rw [e]
  exact Submodule.add_mem _ (colv_mem_Ly u _) (Submodule.smul_mem _ _ (colv_mem_Ly u _))

theorem quad_coeff_mem {S : Submodule ℂ (MF n)} {a₂ a₁ a₀ : MF n} (h₂ : a₂ ∈ S) (h₁ : a₁ ∈ S)
    (h₀ : a₀ ∈ S) (k : ℕ) : (quad a₂ a₁ a₀).coeff k ∈ S := by
  rw [coeff_quad]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;> split_ifs <;>
    first | assumption | exact Submodule.zero_mem _

/-- **A generator in cos/sin form.** -/
theorem exists_gen {s : Set (MF n)} {T : Submodule ℂ (MF n)} {g A B C : MF n}
    (hg : ∀ (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ),
      g ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * X) =
        (Real.cos t : ℂ) * A X + (Real.sin t : ℂ) * B X + C X)
    (hA : A ∈ Submodule.span ℂ s) (hB : B ∈ Submodule.span ℂ s) (hC : C ∈ Submodule.span ℂ s)
    (hT : (1 / 2 : ℂ) • (A - Complex.I • B) ∈ T) :
    ∃ P : Polynomial (MF n), IsExpansion b 1 g P ∧
      (∀ k, P.coeff k ∈ Submodule.span ℂ s) ∧ P.coeff 2 ∈ T := by
  refine ⟨_, isExpansion_of_cos_sin hg, quad_coeff_mem ?_ hC ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hA (Submodule.smul_mem _ _ hB))
  · exact Submodule.smul_mem _ _ (Submodule.add_mem _ hA (Submodule.smul_mem _ _ hB))
  · rw [coeff_quad]
    simpa using hT

theorem hasExpTop_Ly (hb : b + 1 < n) (u : Fin n → ℂ) :
    HasExpTop b 1 (Ly u) (Submodule.span ℂ {yZ hb u}) := by
  refine hasExpTop_span ?_
  rintro _ ⟨i, rfl⟩
  dsimp only
  by_cases h1 : i = ia hb
  · subst h1
    refine exists_gen (A := colv u (ia hb)) (B := -colv u (ib hb)) (C := 0)
      (fun t X => by rw [colv_rot_ia]; simp; ring) (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.neg_mem _ (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.zero_mem _) ?_
    have e : (1 / 2 : ℂ) • (colv u (ia hb) - Complex.I • -colv u (ib hb)) =
        (1 / 2 : ℂ) • yZ hb u := by
      funext X
      simp [yZ]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  by_cases h2 : i = ib hb
  · subst h2
    refine exists_gen (A := colv u (ib hb)) (B := colv u (ia hb)) (C := 0)
      (fun t X => by rw [colv_rot_ib]; simp; ring) (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.subset_span ⟨_, rfl⟩) (Submodule.zero_mem _) ?_
    have e : (1 / 2 : ℂ) • (colv u (ib hb) - Complex.I • colv u (ia hb)) =
        (-Complex.I / 2 : ℂ) • yZ hb u := by
      funext X
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, yZ]
      linear_combination ((1 / 2 : ℂ) * colv u (ib hb) X) * Complex.I_sq
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · refine exists_gen (A := 0) (B := 0) (C := colv u i)
      (fun t X => by rw [colv_rot_of_ne hb u t X h1 h2]; simp) (Submodule.zero_mem _)
      (Submodule.zero_mem _) (Submodule.subset_span ⟨_, rfl⟩) ?_
    simp

theorem hasExpTop_mono {N : ℕ} {S T T' : Submodule ℂ (MF n)} (h : HasExpTop b N S T)
    (hT : T ≤ T') : HasExpTop b N S T' := fun H hH => by
  obtain ⟨P, hP, hPS, hPT⟩ := h H hH
  exact ⟨P, hP, hPS, hT hPT⟩

theorem span_singleton_pow_mul (a c : MF n) (m k : ℕ) :
    Submodule.span ℂ {a} ^ m * Submodule.span ℂ {c} ^ k = Submodule.span ℂ {a ^ m * c ^ k} := by
  rw [Submodule.span_pow, Submodule.span_pow, Set.singleton_pow, Set.singleton_pow,
    Submodule.span_mul_span, Set.singleton_mul_singleton]

end Spans

/-! ## Four coordinates: Plücker coordinates and their self-dual combinations -/

section Four

/-- The Plücker coordinates `y_i z_j - y_j z_i` of the columns `y = X u`, `z = X u'`. -/
def pl (u u' : Fin 4 → ℂ) (i j : Fin 4) : MF 4 :=
  fun X => colv u i X * colv u' j X - colv u j X * colv u' i X

/-- The self-dual combination `w₁ = p₀₁ + p₂₃`. -/
def w1 (u u' : Fin 4 → ℂ) : MF 4 := fun X => pl u u' 0 1 X + pl u u' 2 3 X

/-- The self-dual combination `w₂ = p₀₂ - p₁₃`. -/
def w2 (u u' : Fin 4 → ℂ) : MF 4 := fun X => pl u u' 0 2 X - pl u u' 1 3 X

/-- The self-dual combination `w₃ = p₀₃ + p₁₂`. -/
def w3 (u u' : Fin 4 → ℂ) : MF 4 := fun X => pl u u' 0 3 X + pl u u' 1 2 X

/-- `ν₊ = w₂ + i w₃`, of weight `1` under the rotations of the blocks `0` and `2`. -/
def nup (u u' : Fin 4 → ℂ) : MF 4 := fun X => w2 u u' X + Complex.I * w3 u u' X

/-- `ν₋ = w₂ - i w₃`, of weight `-1` under the rotations of the blocks `0` and `2`. -/
def num (u u' : Fin 4 → ℂ) : MF 4 := fun X => w2 u u' X - Complex.I * w3 u u' X

/-- `w₊ = w₁ + i w₂`, of weight `1` under the rotations of the block `1`. -/
def wp (u u' : Fin 4 → ℂ) : MF 4 := fun X => w1 u u' X + Complex.I * w2 u u' X

theorem h40 : 0 + 1 < 4 := by norm_num

theorem h41 : 1 + 1 < 4 := by norm_num

theorem h42 : 2 + 1 < 4 := by norm_num

theorem colv_rot0 (u : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    colv u 0 ((blockRotation 4 0 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.cos t : ℂ) * colv u 0 X - (Real.sin t : ℂ) * colv u 1 X ∧
      colv u 1 ((blockRotation 4 0 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.sin t : ℂ) * colv u 0 X + (Real.cos t : ℂ) * colv u 1 X ∧
      colv u 2 ((blockRotation 4 0 t : Matrix (Fin 4) (Fin 4) ℝ) * X) = colv u 2 X ∧
      colv u 3 ((blockRotation 4 0 t : Matrix (Fin 4) (Fin 4) ℝ) * X) = colv u 3 X :=
  ⟨colv_rot_ia h40 u t X, colv_rot_ib h40 u t X,
    colv_rot_of_ne h40 u t X (by decide) (by decide),
    colv_rot_of_ne h40 u t X (by decide) (by decide)⟩

theorem colv_rot1 (u : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    colv u 0 ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) * X) = colv u 0 X ∧
      colv u 1 ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.cos t : ℂ) * colv u 1 X - (Real.sin t : ℂ) * colv u 2 X ∧
      colv u 2 ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.sin t : ℂ) * colv u 1 X + (Real.cos t : ℂ) * colv u 2 X ∧
      colv u 3 ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) * X) = colv u 3 X :=
  ⟨colv_rot_of_ne h41 u t X (by decide) (by decide), colv_rot_ia h41 u t X,
    colv_rot_ib h41 u t X, colv_rot_of_ne h41 u t X (by decide) (by decide)⟩

theorem colv_rot2 (u : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    colv u 0 ((blockRotation 4 2 t : Matrix (Fin 4) (Fin 4) ℝ) * X) = colv u 0 X ∧
      colv u 1 ((blockRotation 4 2 t : Matrix (Fin 4) (Fin 4) ℝ) * X) = colv u 1 X ∧
      colv u 2 ((blockRotation 4 2 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.cos t : ℂ) * colv u 2 X - (Real.sin t : ℂ) * colv u 3 X ∧
      colv u 3 ((blockRotation 4 2 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.sin t : ℂ) * colv u 2 X + (Real.cos t : ℂ) * colv u 3 X :=
  ⟨colv_rot_of_ne h42 u t X (by decide) (by decide),
    colv_rot_of_ne h42 u t X (by decide) (by decide), colv_rot_ia h42 u t X,
    colv_rot_ib h42 u t X⟩

theorem sin_sq_add_cos_sq_complex (t : ℝ) : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.sin_sq_add_cos_sq t

theorem w_rot0 (u u' : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    w1 u u' ((blockRotation 4 0 t : Matrix (Fin 4) (Fin 4) ℝ) * X) = w1 u u' X ∧
      w2 u u' ((blockRotation 4 0 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.cos t : ℂ) * w2 u u' X - (Real.sin t : ℂ) * w3 u u' X ∧
      w3 u u' ((blockRotation 4 0 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.sin t : ℂ) * w2 u u' X + (Real.cos t : ℂ) * w3 u u' X := by
  obtain ⟨a0, a1, a2, a3⟩ := colv_rot0 u t X
  obtain ⟨b0, b1, b2, b3⟩ := colv_rot0 u' t X
  have hcs := sin_sq_add_cos_sq_complex t
  simp only [w1, w2, w3, pl, a0, a1, a2, a3, b0, b1, b2, b3]
  refine ⟨?_, by ring, by ring⟩
  linear_combination (colv u 0 X * colv u' 1 X - colv u 1 X * colv u' 0 X) * hcs

theorem w_rot1 (u u' : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    w1 u u' ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.cos t : ℂ) * w1 u u' X - (Real.sin t : ℂ) * w2 u u' X ∧
      w2 u u' ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.sin t : ℂ) * w1 u u' X + (Real.cos t : ℂ) * w2 u u' X ∧
      w3 u u' ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) * X) = w3 u u' X := by
  obtain ⟨a0, a1, a2, a3⟩ := colv_rot1 u t X
  obtain ⟨b0, b1, b2, b3⟩ := colv_rot1 u' t X
  have hcs := sin_sq_add_cos_sq_complex t
  simp only [w1, w2, w3, pl, a0, a1, a2, a3, b0, b1, b2, b3]
  refine ⟨by ring, by ring, ?_⟩
  linear_combination (colv u 1 X * colv u' 2 X - colv u 2 X * colv u' 1 X) * hcs

theorem w_rot2 (u u' : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    w1 u u' ((blockRotation 4 2 t : Matrix (Fin 4) (Fin 4) ℝ) * X) = w1 u u' X ∧
      w2 u u' ((blockRotation 4 2 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.cos t : ℂ) * w2 u u' X - (Real.sin t : ℂ) * w3 u u' X ∧
      w3 u u' ((blockRotation 4 2 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        (Real.sin t : ℂ) * w2 u u' X + (Real.cos t : ℂ) * w3 u u' X := by
  obtain ⟨a0, a1, a2, a3⟩ := colv_rot2 u t X
  obtain ⟨b0, b1, b2, b3⟩ := colv_rot2 u' t X
  have hcs := sin_sq_add_cos_sq_complex t
  simp only [w1, w2, w3, pl, a0, a1, a2, a3, b0, b1, b2, b3]
  refine ⟨?_, by ring, by ring⟩
  linear_combination (colv u 2 X * colv u' 3 X - colv u 3 X * colv u' 2 X) * hcs

theorem nup_rot0 (u u' : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    nup u u' ((blockRotation 4 0 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      expMode 1 t * nup u u' X := by
  obtain ⟨-, h2, h3⟩ := w_rot0 u u' t X
  simp only [nup, h2, h3, expMode_one_eq]
  linear_combination (-(Real.sin t : ℂ) * w3 u u' X) * Complex.I_sq

theorem num_rot0 (u u' : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    num u u' ((blockRotation 4 0 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      expMode (-1) t * num u u' X := by
  obtain ⟨-, h2, h3⟩ := w_rot0 u u' t X
  simp only [num, h2, h3, expMode_neg_one_eq]
  linear_combination (-(Real.sin t : ℂ) * w3 u u' X) * Complex.I_sq

theorem nup_rot2 (u u' : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    nup u u' ((blockRotation 4 2 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      expMode 1 t * nup u u' X := by
  obtain ⟨-, h2, h3⟩ := w_rot2 u u' t X
  simp only [nup, h2, h3, expMode_one_eq]
  linear_combination (-(Real.sin t : ℂ) * w3 u u' X) * Complex.I_sq

theorem num_rot2 (u u' : Fin 4 → ℂ) (t : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    num u u' ((blockRotation 4 2 t : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      expMode (-1) t * num u u' X := by
  obtain ⟨-, h2, h3⟩ := w_rot2 u u' t X
  simp only [num, h2, h3, expMode_neg_one_eq]
  linear_combination (-(Real.sin t : ℂ) * w3 u u' X) * Complex.I_sq

theorem colv_diag4 (u : Fin 4 → ℂ) (s : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) :
    colv u i (Matrix.diagonal s * X) = (s i : ℂ) * colv u i X :=
  colv_diag u i s X

/-- The span `L_w` of `w₁, w₂, w₃`. -/
def Lw (u u' : Fin 4 → ℂ) : Submodule ℂ (MF 4) :=
  Submodule.span ℂ {w1 u u', w2 u u', w3 u u'}

theorem w1_mem_Lw (u u' : Fin 4 → ℂ) : w1 u u' ∈ Lw u u' :=
  Submodule.subset_span (by simp)

theorem w2_mem_Lw (u u' : Fin 4 → ℂ) : w2 u u' ∈ Lw u u' :=
  Submodule.subset_span (by simp)

theorem w3_mem_Lw (u u' : Fin 4 → ℂ) : w3 u u' ∈ Lw u u' :=
  Submodule.subset_span (by simp)

theorem nup_mem_Lw (u u' : Fin 4 → ℂ) : nup u u' ∈ Lw u u' := by
  have e : nup u u' = w2 u u' + Complex.I • w3 u u' := by
    funext X
    simp [nup]
  rw [e]
  exact Submodule.add_mem _ (w2_mem_Lw u u') (Submodule.smul_mem _ _ (w3_mem_Lw u u'))

theorem num_mem_Lw (u u' : Fin 4 → ℂ) : num u u' ∈ Lw u u' := by
  have e : num u u' = w2 u u' + (-Complex.I) • w3 u u' := by
    funext X
    simp [num, sub_eq_add_neg]
  rw [e]
  exact Submodule.add_mem _ (w2_mem_Lw u u') (Submodule.smul_mem _ _ (w3_mem_Lw u u'))

theorem hasExpTop_Lw1 (u u' : Fin 4 → ℂ) :
    HasExpTop 1 1 (Lw u u') (Submodule.span ℂ {wp u u'}) := by
  refine hasExpTop_span ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · refine exists_gen (A := w1 u u') (B := -w2 u u') (C := 0)
      (fun t X => by rw [(w_rot1 u u' t X).1]; simp; ring) (w1_mem_Lw u u')
      (Submodule.neg_mem _ (w2_mem_Lw u u')) (Submodule.zero_mem _) ?_
    have e : (1 / 2 : ℂ) • (w1 u u' - Complex.I • -w2 u u') = (1 / 2 : ℂ) • wp u u' := by
      funext X
      simp [wp]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · refine exists_gen (A := w2 u u') (B := w1 u u') (C := 0)
      (fun t X => by rw [(w_rot1 u u' t X).2.1]; simp; ring) (w2_mem_Lw u u')
      (w1_mem_Lw u u') (Submodule.zero_mem _) ?_
    have e : (1 / 2 : ℂ) • (w2 u u' - Complex.I • w1 u u') = (-Complex.I / 2 : ℂ) • wp u u' := by
      funext X
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, wp]
      linear_combination ((1 / 2 : ℂ) * w2 u u' X) * Complex.I_sq
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · refine exists_gen (A := 0) (B := 0) (C := w3 u u')
      (fun t X => by rw [(w_rot1 u u' t X).2.2]; simp) (Submodule.zero_mem _)
      (Submodule.zero_mem _) (w3_mem_Lw u u') ?_
    simp

theorem hasExpTop_Lw0 (u u' : Fin 4 → ℂ) : HasExpTop 0 1 (Lw u u') ⊤ := by
  refine hasExpTop_span ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact exists_gen (A := 0) (B := 0) (C := w1 u u')
      (fun t X => by rw [(w_rot0 u u' t X).1]; simp) (Submodule.zero_mem _)
      (Submodule.zero_mem _) (w1_mem_Lw u u') Submodule.mem_top
  · exact exists_gen (A := w2 u u') (B := -w3 u u') (C := 0)
      (fun t X => by rw [(w_rot0 u u' t X).2.1]; simp; ring) (w2_mem_Lw u u')
      (Submodule.neg_mem _ (w3_mem_Lw u u')) (Submodule.zero_mem _) Submodule.mem_top
  · exact exists_gen (A := w3 u u') (B := w2 u u') (C := 0)
      (fun t X => by rw [(w_rot0 u u' t X).2.2]; simp; ring) (w3_mem_Lw u u')
      (w2_mem_Lw u u') (Submodule.zero_mem _) Submodule.mem_top

theorem hasExpTop_Lw2 (u u' : Fin 4 → ℂ) : HasExpTop 2 1 (Lw u u') ⊤ := by
  refine hasExpTop_span ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact exists_gen (A := 0) (B := 0) (C := w1 u u')
      (fun t X => by rw [(w_rot2 u u' t X).1]; simp) (Submodule.zero_mem _)
      (Submodule.zero_mem _) (w1_mem_Lw u u') Submodule.mem_top
  · exact exists_gen (A := w2 u u') (B := -w3 u u') (C := 0)
      (fun t X => by rw [(w_rot2 u u' t X).2.1]; simp; ring) (w2_mem_Lw u u')
      (Submodule.neg_mem _ (w3_mem_Lw u u')) (Submodule.zero_mem _) Submodule.mem_top
  · exact exists_gen (A := w3 u u') (B := w2 u u') (C := 0)
      (fun t X => by rw [(w_rot2 u u' t X).2.2]; simp; ring) (w3_mem_Lw u u')
      (w2_mem_Lw u u') (Submodule.zero_mem _) Submodule.mem_top

/-- The submodule `S = L_y^r L_w^m` of the products of `r` column functions of `u` and `m`
self-dual combinations. -/
def Sm (u u' : Fin 4 → ℂ) (r m : ℕ) : Submodule ℂ (MF 4) := Ly u ^ r * Lw u u' ^ m

theorem hasExpTop_Sm1 (u u' : Fin 4 → ℂ) (r m : ℕ) :
    HasExpTop 1 (r + m) (Sm u u' r m) (Submodule.span ℂ {yZ h41 u ^ r * wp u u' ^ m}) := by
  have h := hasExpTop_mul (hasExpTop_pow (hasExpTop_Ly h41 u) r) (hasExpTop_pow
    (hasExpTop_Lw1 u u') m)
  rw [mul_one, mul_one, span_singleton_pow_mul] at h
  exact h

theorem hasExpTop_Sm0 (u u' : Fin 4 → ℂ) (r m : ℕ) : HasExpTop 0 (r + m) (Sm u u' r m) ⊤ := by
  have h := hasExpTop_mul (hasExpTop_pow (hasExpTop_mono (hasExpTop_Ly h40 u) le_top) r)
    (hasExpTop_pow (hasExpTop_Lw0 u u') m)
  rw [mul_one, mul_one] at h
  exact hasExpTop_mono h le_top

theorem hasExpTop_Sm2 (u u' : Fin 4 → ℂ) (r m : ℕ) : HasExpTop 2 (r + m) (Sm u u' r m) ⊤ := by
  have h := hasExpTop_mul (hasExpTop_pow (hasExpTop_mono (hasExpTop_Ly h42 u) le_top) r)
    (hasExpTop_pow (hasExpTop_Lw2 u u') m)
  rw [mul_one, mul_one] at h
  exact hasExpTop_mono h le_top

theorem pl_mem_PF (u u' : Fin 4 → ℂ) (i j : Fin 4) : pl u u' i j ∈ PF 4 :=
  Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (colv_mem_PF u i) (colv_mem_PF u' j))
    (Subalgebra.mul_mem _ (colv_mem_PF u j) (colv_mem_PF u' i))

theorem w1_mem_PF (u u' : Fin 4 → ℂ) : w1 u u' ∈ PF 4 :=
  Subalgebra.add_mem _ (pl_mem_PF u u' 0 1) (pl_mem_PF u u' 2 3)

theorem w2_mem_PF (u u' : Fin 4 → ℂ) : w2 u u' ∈ PF 4 :=
  Subalgebra.sub_mem _ (pl_mem_PF u u' 0 2) (pl_mem_PF u u' 1 3)

theorem w3_mem_PF (u u' : Fin 4 → ℂ) : w3 u u' ∈ PF 4 :=
  Subalgebra.add_mem _ (pl_mem_PF u u' 0 3) (pl_mem_PF u u' 1 2)

end Four

end RealInterlacedJacquet

end Langlands.Archimedean
