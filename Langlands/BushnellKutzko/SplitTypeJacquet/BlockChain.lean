import Langlands.BushnellKutzko.SplittingBasis

/-! # Coordinate lattice chains with prescribed jumps -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uI

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {π : 𝒪[F]} (hπ : Irreducible π)
  {I : Type uI} [Fintype I] {e : ℕ} (a : I → Fin e)

private def blockScaling (i : ℤ) : (I → F) ≃ₗ[F] (I → F) :=
  LinearEquiv.piCongrRight fun k => LinearEquiv.smulOfNeZero F F
    ((π : F) ^ (-((((a k : ℕ) : ℤ) - i) / (e : ℤ))))
    (zpow_ne_zero _ (coe_uniformizer_ne_zero hπ))

private def blockLattice (i : ℤ) : Submodule 𝒪[F] (I → F) :=
  (standardLattice F I).map ((blockScaling hπ a i).toLinearMap.restrictScalars 𝒪[F])

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem blockLattice_isLattice (i : ℤ) : (blockLattice hπ a i).IsLattice F := by
  let d := blockScaling hπ a i
  have h : (standardLattice F I).IsLattice F := inferInstance
  refine ⟨h.fg.map _, ?_⟩
  rw [blockLattice, Submodule.map_coe]
  change Submodule.span F (d.toLinearMap '' (standardLattice F I : Set (I → F))) = ⊤
  rw [← Submodule.map_span, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact d.surjective

omit [Fintype I] in
private theorem mem_blockLattice (he : 0 < e) (i : ℤ) (v : I → F) :
    v ∈ blockLattice hπ a i ↔
      ∀ k, v k ≠ 0 → i ≤ (a k : ℕ) + (e : ℤ) * ordOf hπ (v k) := by
  let t (k : I) : ℤ := (((a k : ℕ) : ℤ) - i) / e
  let w : I → F := fun k => (π : F) ^ t k * v k
  let d := blockScaling hπ a i
  have hπ₀ := coe_uniformizer_ne_zero hπ
  have hw : d w = v := by
    funext k
    change (π : F) ^ (-t k) * ((π : F) ^ t k * v k) = v k
    rw [← mul_assoc, ← zpow_add₀ hπ₀, neg_add_cancel, zpow_zero, one_mul]
  have hi : v ∈ blockLattice hπ a i ↔ ∀ k, w k ∈ 𝒪[F] := by
    change v ∈ (standardLattice F I).map (d.toLinearMap.restrictScalars 𝒪[F]) ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, hxd⟩
      have h := d.injective (hxd.trans hw.symm)
      exact mem_standardLattice.mp (h ▸ hx)
    · intro h
      exact ⟨w, mem_standardLattice.mpr h, hw⟩
  rw [hi]
  apply forall_congr'
  intro k
  by_cases hk : v k = 0
  · simp [w, hk]
  have hn : w k ≠ 0 := mul_ne_zero (zpow_ne_zero _ hπ₀) hk
  have he' : 0 < (e : ℤ) := by exact_mod_cast he
  rw [mem_integer_iff_ordOf_nonneg hπ hn]
  change 0 ≤ ordOf hπ ((π : F) ^ t k * v k) ↔ _
  rw [ordOf_mul hπ (zpow_ne_zero _ hπ₀) hk, ordOf_zpow, ← neg_le_iff_add_nonneg,
    show t k = (((a k : ℕ) : ℤ) - i) / e from rfl, Int.le_ediv_iff_mul_le he']
  simp only [hk, ne_eq, not_false_eq_true, true_implies, neg_mul,
    mul_comm (ordOf hπ (v k))]
  omega

omit [Fintype I] in
private theorem blockLattice_add_period (he : 0 < e) (i : ℤ) :
    blockLattice hπ a (i + e) = Ring.jacobson 𝒪[F] • blockLattice hπ a i := by
  have hsmul (v : I → F) :
      (π : F) • v ∈ blockLattice hπ a (i + e) ↔ v ∈ blockLattice hπ a i := by
    rw [mem_blockLattice hπ a he, mem_blockLattice hπ a he]
    apply forall_congr'
    intro k
    have hπ₀ := coe_uniformizer_ne_zero hπ
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hk : v k = 0
    · simp [hk]
    have hπord : ordOf hπ (π : F) = 1 := by simpa using ordOf_zpow hπ 1
    simp only [mul_ne_zero hπ₀ hk, hk, ne_eq, not_false_eq_true, true_implies,
      ordOf_mul hπ hπ₀ hk, hπord, mul_add, mul_one]
    omega
  rw [jacobson_integer_eq_maximalIdeal, hπ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  change v ∈ blockLattice hπ a (i + e) ↔ ∃ w ∈ blockLattice hπ a i, (π : F) • w = v
  constructor
  · intro hv
    let w := (π : F)⁻¹ • v
    have hw : (π : F) • w = v := smul_inv_smul₀ (coe_uniformizer_ne_zero hπ) _
    exact ⟨w, (hsmul w).mp (hw ▸ hv), hw⟩
  · rintro ⟨w, hw, rfl⟩
    exact (hsmul w).mpr hw

/-- The coordinate chain in which the coordinates indexed by `a k = j`
are multiplied by the uniformizer at step `j` in every period. -/
def blockChain (he : 0 < e) (ha : Function.Surjective a) : LatticeChain 𝒪[F] F (I → F) where
  lattice := blockLattice hπ a
  isLattice := blockLattice_isLattice hπ a
  lattice_succ_lt i := by
    classical
    have he' : 0 < (e : ℤ) := by exact_mod_cast he
    let j : Fin e := ⟨(i % (e : ℤ)).toNat, by
      have h := Int.emod_lt_of_pos i he'
      omega⟩
    obtain ⟨k, hk⟩ := ha j
    have hj : ((j : ℕ) : ℤ) = i % (e : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg i he'.ne')
    let x : F := (π : F) ^ (i / (e : ℤ))
    let v : I → F := Pi.single k x
    have hx : x ≠ 0 := zpow_ne_zero _ (coe_uniformizer_ne_zero hπ)
    have hval : ((a k : ℕ) : ℤ) + e * ordOf hπ x = i := by
      rw [hk, hj, show ordOf hπ x = i / (e : ℤ) from ordOf_zpow hπ _]
      exact Int.emod_add_mul_ediv i e
    apply IsConcreteLE.lt_iff_le_and_exists.mpr
    refine ⟨fun w hw => (mem_blockLattice hπ a he i w).mpr
      (fun l hl => (show i ≤ i + 1 by omega).trans
        ((mem_blockLattice hπ a he (i + 1) w).mp hw l hl)), v, ?_, ?_⟩
    · apply (mem_blockLattice hπ a he i v).mpr
      intro l hl
      have hlk : l = k := by
        by_contra h
        exact hl (by simp [v, Pi.single_eq_of_ne h])
      subst l
      simpa only [v, Pi.single_eq_same, hval] using le_rfl (a := i)
    · intro hv
      have h := (mem_blockLattice hπ a he (i + 1) v).mp hv k (by simpa [v] using hx)
      rw [show v k = x by simp [v], hval] at h
      omega
  exists_period := ⟨e, he, blockLattice_add_period hπ a he⟩

variable (he : 0 < e) (ha : Function.Surjective a)

theorem period_blockChain : (blockChain hπ a he ha).period = e :=
  ((blockChain hπ a he ha).period_unique (blockLattice_add_period hπ a he)).symm

theorem mem_blockChain (i : ℤ) (v : I → F) :
    v ∈ (blockChain hπ a he ha).lattice i ↔
      ∀ k, v k ≠ 0 → i ≤ (a k : ℕ) + (e : ℤ) * ordOf hπ (v k) :=
  mem_blockLattice hπ a he i v

/-- At step zero all coordinates range over the valuation ring. -/
theorem blockChain_lattice_zero :
    (blockChain hπ a he ha).lattice 0 = standardLattice F I := by
  ext v
  rw [mem_blockChain, mem_standardLattice]
  apply forall_congr'
  intro k
  by_cases hk : v k = 0
  · simp [hk]
  rw [mem_integer_iff_ordOf_nonneg hπ hk]
  simp only [hk, ne_eq, not_false_eq_true, true_implies]
  have hak : ((a k : ℕ) : ℤ) < (e : ℤ) := by exact_mod_cast (a k).isLt
  have he₀ : (0 : ℤ) ≤ e := by positivity
  constructor
  · intro h
    by_contra! hneg
    have hmul := mul_le_mul_of_nonneg_left (show ordOf hπ (v k) ≤ -1 by omega) he₀
    simp only [mul_neg, mul_one] at hmul
    omega
  · intro h
    exact add_nonneg (by positivity) (mul_nonneg he₀ h)

end Langlands.BushnellKutzko.LatticeChain
