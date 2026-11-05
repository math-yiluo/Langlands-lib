import Langlands.Global.AdelicGLStandardCompact
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.Global.ArchimedeanCompactMaximalityProof
import Langlands.Global.AdelicIwasawaStatement
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.InfinitePlaceLeviIwasawaBaseChange

/-! # Maximality of the standard compact subgroup of the actual adelic `GL(n)` -/

noncomputable section

universe u

open scoped Matrix
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.PrimitiveAdelicHeight

/-! ## Compact overgroups of the integral matrices over a normed field -/

section Local

variable {𝕜 : Type*} [NormedField 𝕜] {n : ℕ}

/-- The gauge `x ↦ sup_{h ∈ H} ‖h x‖` of a subgroup `H`, for the sup norm on `𝕜ⁿ`. -/
def supGauge (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) 𝕜)) (x : Fin n → 𝕜) : ℝ :=
  ⨆ h : H, ‖((h : Matrix.GeneralLinearGroup (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x‖

variable {H : Subgroup (Matrix.GeneralLinearGroup (Fin n) 𝕜)}

/-- A compact subgroup moves each vector within a bounded set of norms. -/
theorem bddAbove_supGauge
    (hH : IsCompact (H : Set (Matrix.GeneralLinearGroup (Fin n) 𝕜))) (x : Fin n → 𝕜) :
    BddAbove (Set.range fun h : H =>
      ‖((h : Matrix.GeneralLinearGroup (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x‖) := by
  have hc : Continuous (fun g : Matrix.GeneralLinearGroup (Fin n) 𝕜 =>
      ‖(g : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x‖) :=
    (Units.continuous_val.matrix_mulVec continuous_const).norm
  have h := hH.bddAbove_image hc.continuousOn
  rw [Set.image_eq_range] at h
  exact h

/-- The gauge of a compact subgroup dominates the sup norm. -/
theorem le_supGauge
    (hH : IsCompact (H : Set (Matrix.GeneralLinearGroup (Fin n) 𝕜))) (x : Fin n → 𝕜) :
    ‖x‖ ≤ supGauge H x := by
  have h := le_ciSup (bddAbove_supGauge hH x) (1 : H)
  unfold supGauge
  refine le_trans (le_of_eq ?_) h
  simp

/-- The gauge of `H` is invariant under the elements of `H`. -/
theorem supGauge_mulVec {k : Matrix.GeneralLinearGroup (Fin n) 𝕜} (hk : k ∈ H)
    (x : Fin n → 𝕜) :
    supGauge H ((k : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x) = supGauge H x := by
  unfold supGauge
  simp only [Matrix.mulVec_mulVec]
  exact (Equiv.mulRight (⟨k, hk⟩ : H)).iSup_comp (g := fun h : H =>
    ‖((h : Matrix.GeneralLinearGroup (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x‖)

/-- The gauge is absolutely homogeneous. -/
theorem supGauge_smul (c : 𝕜) (x : Fin n → 𝕜) : supGauge H (c • x) = ‖c‖ * supGauge H x := by
  unfold supGauge
  simp only [Matrix.mulVec_smul, norm_smul]
  exact (Real.mul_iSup_of_nonneg (norm_nonneg c) _).symm

/-- If the closed unit ball `O` of a normed field is a subring, then every compact subgroup
of `GL n` containing all matrices invertible over `O` consists of matrices with entries
in `O`. -/
theorem mem_of_isCompact_of_integral_le (O : Subring 𝕜) (hO : ∀ x, x ∈ O ↔ ‖x‖ ≤ 1)
    (hH : IsCompact (H : Set (Matrix.GeneralLinearGroup (Fin n) 𝕜)))
    (hle : ∀ g : Matrix.GeneralLinearGroup (Fin n) 𝕜,
      (∀ i j, g i j ∈ O) → (∀ i j, g⁻¹ i j ∈ O) → g ∈ H)
    {h : Matrix.GeneralLinearGroup (Fin n) 𝕜} (hh : h ∈ H) (a j : Fin n) : h a j ∈ O := by
  classical
  rw [hO]
  have : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨e, he⟩ : ∃ e : Fin n → 𝕜, e = Pi.single j 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin n → 𝕜, y = (h : Matrix (Fin n) (Fin n) 𝕜) *ᵥ e := ⟨_, rfl⟩
  have hya : ∀ b, y b = h b j := fun b => by
    rw [hy, he, Matrix.mulVec_single_one]
    rfl
  obtain ⟨i0, hi0⟩ := Finite.exists_max fun b => ‖y b‖
  obtain ⟨c, hcy⟩ : ∃ c, c = y i0 := ⟨_, rfl⟩
  have hc : c ≠ 0 := by
    intro hc0
    have hy0 : y = 0 := funext fun b =>
      norm_le_zero_iff.mp ((hi0 b).trans_eq (by rw [← hcy, hc0, norm_zero]))
    have h1 : ((h⁻¹ : Matrix.GeneralLinearGroup (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) *ᵥ y =
        e := by
      rw [hy, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have h2 := congrFun h1 j
    rw [hy0, Matrix.mulVec_zero, he] at h2
    simp at h2
  obtain ⟨z, hz⟩ : ∃ z : Fin n → 𝕜, z = c⁻¹ • y := ⟨_, rfl⟩
  have hzO : ∀ b, z b ∈ O := fun b => by
    rw [hO, hz, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact (inv_mul_le_one₀ (norm_pos_iff.mpr hc)).mpr (hcy ▸ hi0 b)
  have hzi0 : z i0 = 1 := by
    rw [hz, Pi.smul_apply, smul_eq_mul, ← hcy, inv_mul_cancel₀ hc]
  -- An integral matrix with integral inverse whose `j`-th column is `z`.
  let A : Matrix (Fin n) (Fin n) 𝕜 :=
    ((1 : Matrix (Fin n) (Fin n) 𝕜).updateCol i0 z).submatrix id (Equiv.swap i0 j)
  have hAe : A *ᵥ e = z := by
    rw [he, Matrix.mulVec_single_one]
    ext b
    simp [A]
  have hdet1 : ((1 : Matrix (Fin n) (Fin n) 𝕜).updateCol i0 z).det = z i0 := by
    have h1 := Matrix.det_updateCol_sum (1 : Matrix (Fin n) (Fin n) 𝕜) i0 z
    simpa [Matrix.one_apply] using h1
  have hAnorm : ‖A.det‖ = 1 := by
    simp only [A]
    rw [Matrix.det_permute', hdet1, hzi0, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i0 j)) with hs | hs <;>
      simp [hs]
  have hAO : ∀ a b, A a b ∈ O := by
    intro a b
    simp only [A, Matrix.submatrix_apply, id, Matrix.updateCol_apply, Matrix.one_apply]
    split_ifs
    · exact hzO a
    · exact O.one_mem
    · exact O.zero_mem
  have hdetne : A.det ≠ 0 := norm_ne_zero_iff.mp (by rw [hAnorm]; exact one_ne_zero)
  let k := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetne
  have hk : k ∈ H := by
    refine hle k hAO fun a b => ?_
    rw [Matrix.coe_units_inv]
    exact inv_mem_of_forall_mem O hAO (by rw [hO, norm_inv, hAnorm, inv_one]) a b
  have hN : supGauge H e = ‖c‖ * supGauge H e := by
    calc supGauge H e = supGauge H y := by rw [hy, supGauge_mulVec hh e]
      _ = supGauge H (c • z) := by rw [hz, smul_inv_smul₀ hc]
      _ = ‖c‖ * supGauge H z := supGauge_smul c z
      _ = ‖c‖ * supGauge H e := by rw [← hAe]; exact congrArg (‖c‖ * ·) (supGauge_mulVec hk e)
  have hpos : 0 < supGauge H e := by
    refine zero_lt_one.trans_le (le_trans ?_ (le_supGauge hH e))
    rw [he]
    have h1 := norm_le_pi_norm (Pi.single j 1 : Fin n → 𝕜) j
    rwa [Pi.single_eq_same, norm_one] at h1
  have hc1 : ‖c‖ = 1 := by
    exact mul_right_cancel₀ hpos.ne' (by rw [one_mul]; exact hN.symm)
  rw [← hya a, ← hc1, hcy]
  exact hi0 a

end Local

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-! ## Finite places -/

/-- The integral subgroup `GL n (O_v)` is maximal among the compact subgroups of
`GL n (F_v)` at every finite place `v`. -/
theorem localIntegral_maximal (v : FinitePlace F)
    (H : Subgroup (FiniteLocalGL F n v)) (hH : IsCompact (H : Set (FiniteLocalGL F n v)))
    (hle : (FiniteAdelicGL.localIntegral F n v).toSubgroup ≤ H) :
    H = (FiniteAdelicGL.localIntegral F n v).toSubgroup := by
  have hO : ∀ x : FiniteCompletion F v,
      x ∈ (v.adicCompletionIntegers F).toSubring ↔ ‖x‖ ≤ 1 := fun x => by
    rw [ValuationSubring.mem_toSubring,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
  have hle' : ∀ g : FiniteLocalGL F n v,
      (∀ i j, g i j ∈ (v.adicCompletionIntegers F).toSubring) →
        (∀ i j, g⁻¹ i j ∈ (v.adicCompletionIntegers F).toSubring) → g ∈ H :=
    fun g h1 h2 => hle ⟨h1, h2⟩
  refine le_antisymm (fun g hg => ?_) hle
  exact ⟨fun i j => mem_of_isCompact_of_integral_le _ hO hH hle' hg i j,
    fun i j => mem_of_isCompact_of_integral_le _ hO hH hle' (H.inv_mem hg) i j⟩

/-! ## Assembly -/

/-- The standard compact subgroup of the actual adelic `GL(n)` is maximal among its compact
subgroups: every compact subgroup containing it equals it. -/
theorem standardCompact_maximal (L : Subgroup (AdelicGL F n))
    (hL : IsCompact (L : Set (AdelicGL F n))) (hle : standardCompact F n ≤ L) :
    L = standardCompact F n := by
  refine le_antisymm (fun g hg => ?_) hle
  rw [mem_standardCompact_iff]
  constructor
  · let U := L.map (AdelicGL.infinite F n).toMonoidHom
    have hU : IsCompact (U : Set (InfiniteAdelicGL F n)) := by
      rw [Subgroup.coe_map]
      exact hL.image (AdelicGL.infinite F n).continuous
    have hstd : standardInfiniteCompact F n ≤ U := fun κ hκ => by
      refine ⟨AdelicGL.pair F n κ 1, hle ?_, by simp⟩
      rw [mem_standardCompact_iff]
      simpa using hκ
    have hU' := standardInfiniteCompactMaximality F n U hU hstd
    rw [← hU']
    exact ⟨g, hg, rfl⟩
  · rw [FiniteAdelicGL.mem_standardIntegral_iff_local]
    intro v
    let f := (FiniteAdelicGL.localProjection F n v).toMonoidHom.comp
      (AdelicGL.finite F n).toMonoidHom
    let H := L.map f
    have hH : IsCompact (H : Set (FiniteLocalGL F n v)) := by
      rw [Subgroup.coe_map]
      exact hL.image ((FiniteAdelicGL.localProjection F n v).continuous.comp
        (AdelicGL.finite F n).continuous)
    have hloc : (FiniteAdelicGL.localIntegral F n v).toSubgroup ≤ H := fun k hk => by
      refine ⟨AdelicGL.pair F n 1 (FiniteAdelicGL.localInclusion F n v k), hle ?_, ?_⟩
      · rw [mem_standardCompact_iff]
        refine ⟨by simp, ?_⟩
        rw [AdelicGL.finite_pair, FiniteAdelicGL.localInclusion_mem_standardIntegral]
        exact hk
      · simp [f]
    have hH' := localIntegral_maximal F n v H hH hloc
    have hg' : f g ∈ H := ⟨g, hg, rfl⟩
    rw [hH'] at hg'
    exact hg'

/-- Compactness together with maximality among compact subgroups. -/
theorem isMaximalCompact_standardCompact :
    CompactIwasawa.IsMaximalCompact (standardCompact F n) :=
  ⟨isCompact_standardCompact F n, standardCompact_maximal F n⟩

/-- The standard compact subgroup, transported to the actual adelic points of the general
linear group scheme over `F`, is a maximal compact subgroup there. -/
theorem isMaximalCompactSubgroup_generalLinear :
    AdelicGroupPoints.IsMaximalCompactSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ((standardCompact F n).map
        (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.toMonoidHom) :=
  (isMaximalCompact_standardCompact F n).map (GeneralLinearGroupPoints.adelicHomeomorph F n).symm

end Langlands.Global.PrimitiveAdelicHeight
