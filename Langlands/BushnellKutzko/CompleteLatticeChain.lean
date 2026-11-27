import Langlands.BushnellKutzko.SplittingBasis

/-! # The complete lattice chain of an ordered basis -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {π : 𝒪[F]} (hπ : Irreducible π)
  {d : ℕ} (hd : 0 < d)

private def flagDiagonal (i : ℤ) : (Fin d → F) ≃ₗ[F] (Fin d → F) :=
  LinearEquiv.piCongrRight fun j => LinearEquiv.smulOfNeZero F F
    ((π : F) ^ (-((((j : ℕ) : ℤ) - i) / (d : ℤ)))) (zpow_ne_zero _ (coe_uniformizer_ne_zero hπ))

private def flagLattice (i : ℤ) : Submodule 𝒪[F] (Fin d → F) :=
  (standardLattice F (Fin d)).map ((flagDiagonal hπ i).toLinearMap.restrictScalars 𝒪[F])

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem flagLattice_isLattice (i : ℤ) : (flagLattice hπ (d := d) i).IsLattice F := by
  let b := flagDiagonal hπ (d := d) i
  have h : (standardLattice F (Fin d)).IsLattice F := inferInstance
  refine ⟨h.fg.map _, ?_⟩
  rw [flagLattice, Submodule.map_coe]
  change Submodule.span F (b.toLinearMap '' (standardLattice F (Fin d) : Set (Fin d → F))) = ⊤
  rw [← Submodule.map_span, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact b.surjective

include hd in
private theorem mem_flagLattice_iff (i : ℤ) (v : Fin d → F) :
    v ∈ flagLattice hπ i ↔
      ∀ j, v j ≠ 0 → i ≤ (j : ℕ) + (d : ℤ) * ordOf hπ (v j) := by
  let t (j : Fin d) : ℤ := (((j : ℕ) : ℤ) - i) / d
  let w : Fin d → F := fun j => (π : F) ^ t j * v j
  let b := flagDiagonal hπ (d := d) i
  have hπ₀ := coe_uniformizer_ne_zero hπ
  have hw : b w = v := by
    funext j
    change (π : F) ^ (-t j) * ((π : F) ^ t j * v j) = v j
    rw [← mul_assoc, ← zpow_add₀ hπ₀, neg_add_cancel, zpow_zero, one_mul]
  have hint : v ∈ flagLattice hπ i ↔ ∀ j, w j ∈ 𝒪[F] := by
    change v ∈ (standardLattice F (Fin d)).map (b.toLinearMap.restrictScalars 𝒪[F]) ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, ha'⟩
      have he : a = w := b.injective (ha'.trans hw.symm)
      exact mem_standardLattice.mp (he ▸ ha)
    · intro h
      exact ⟨w, mem_standardLattice.mpr h, hw⟩
  rw [hint]
  apply forall_congr'
  intro j
  by_cases hj : v j = 0
  · simp [w, hj]
  have hn : w j ≠ 0 := mul_ne_zero (zpow_ne_zero _ hπ₀) hj
  have hd' : 0 < (d : ℤ) := by exact_mod_cast hd
  rw [mem_integer_iff_ordOf_nonneg hπ hn]
  change 0 ≤ ordOf hπ ((π : F) ^ t j * v j) ↔ _
  rw [ordOf_mul hπ (zpow_ne_zero _ hπ₀) hj, ordOf_zpow, ← neg_le_iff_add_nonneg,
    show t j = (((j : ℕ) : ℤ) - i) / d from rfl, Int.le_ediv_iff_mul_le hd']
  simp only [hj, ne_eq, not_false_eq_true, true_implies, neg_mul, mul_comm (ordOf hπ (v j))]
  omega

include hd in
private theorem uniformizer_smul_mem_flagLattice_iff (i : ℤ) (v : Fin d → F) :
    (π : F) • v ∈ flagLattice hπ (i + d) ↔ v ∈ flagLattice hπ i := by
  rw [mem_flagLattice_iff hπ hd, mem_flagLattice_iff hπ hd]
  apply forall_congr'
  intro j
  have hπ₀ := coe_uniformizer_ne_zero hπ
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hj : v j = 0
  · simp [hj]
  have hπord : ordOf hπ (π : F) = 1 := by simpa using ordOf_zpow hπ 1
  simp only [mul_ne_zero hπ₀ hj, hj, ne_eq, not_false_eq_true,
    true_implies, ordOf_mul hπ hπ₀ hj, hπord, mul_add, mul_one]
  omega

include hd in
private theorem flagLattice_add_period (i : ℤ) :
    flagLattice hπ (d := d) (i + d) = Ring.jacobson 𝒪[F] • flagLattice hπ i := by
  rw [jacobson_integer_eq_maximalIdeal, hπ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  change v ∈ flagLattice hπ (i + d) ↔ ∃ w ∈ flagLattice hπ i, (π : F) • w = v
  constructor
  · intro hv
    let w := (π : F)⁻¹ • v
    have hw : (π : F) • w = v := smul_inv_smul₀ (coe_uniformizer_ne_zero hπ) _
    exact ⟨w, (uniformizer_smul_mem_flagLattice_iff hπ hd i w).mp (hw ▸ hv), hw⟩
  · rintro ⟨w, hw, rfl⟩
    exact (uniformizer_smul_mem_flagLattice_iff hπ hd i w).mpr hw

/-- The standard complete chain in dimension `d`. In each period one
coordinate is multiplied by the uniformizer at every step. -/
def completeChain : LatticeChain 𝒪[F] F (Fin d → F) where
  lattice := flagLattice hπ
  isLattice := flagLattice_isLattice hπ
  lattice_succ_lt i := by
    classical
    have hd' : 0 < (d : ℤ) := by exact_mod_cast hd
    let j : Fin d := ⟨(i % (d : ℤ)).toNat, by
      have h := Int.emod_lt_of_pos i hd'
      omega⟩
    have hj : ((j : ℕ) : ℤ) = i % (d : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg i hd'.ne')
    let x : F := (π : F) ^ (i / (d : ℤ))
    let v : Fin d → F := Pi.single j x
    have hx : x ≠ 0 := zpow_ne_zero _ (coe_uniformizer_ne_zero hπ)
    have hval : ((j : ℕ) : ℤ) + d * ordOf hπ x = i := by
      rw [hj, show ordOf hπ x = i / (d : ℤ) from ordOf_zpow hπ _]
      exact Int.emod_add_mul_ediv i d
    apply IsConcreteLE.lt_iff_le_and_exists.mpr
    refine ⟨fun w hw => (mem_flagLattice_iff hπ hd i w).mpr
      (fun k hk => (show i ≤ i + 1 by omega).trans
        ((mem_flagLattice_iff hπ hd (i + 1) w).mp hw k hk)),
      v, ?_, ?_⟩
    · apply (mem_flagLattice_iff hπ hd i v).mpr
      intro k hk
      have hkj : k = j := by
        by_contra h
        exact hk (by simp [v, Pi.single_eq_of_ne h])
      subst k
      simpa only [v, Pi.single_eq_same, hval] using le_rfl (a := i)
    · intro hv
      have h := (mem_flagLattice_iff hπ hd (i + 1) v).mp hv j (by simpa [v] using hx)
      rw [show v j = x by simp [v], hval] at h
      omega
  exists_period := ⟨d, hd, flagLattice_add_period hπ hd⟩

/-- The complete chain has period equal to the number of coordinates. -/
theorem period_completeChain : (completeChain hπ hd).period = d :=
  ((completeChain hπ hd).period_unique (flagLattice_add_period hπ hd)).symm

/-- Membership in the complete chain is the coordinate valuation condition. -/
theorem mem_completeChain (i : ℤ) (v : Fin d → F) :
    v ∈ (completeChain hπ hd).lattice i ↔
      ∀ j, v j ≠ 0 → i ≤ (j : ℕ) + (d : ℤ) * ordOf hπ (v j) :=
  mem_flagLattice_iff hπ hd i v

end Langlands.BushnellKutzko.LatticeChain
