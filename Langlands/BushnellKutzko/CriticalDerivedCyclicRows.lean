import Langlands.BushnellKutzko.CriticalDerivedNormalization
import Langlands.BushnellKutzko.CriticalDerivedLeadingCommutation
import Langlands.BushnellKutzko.LatticeChainLayerLift

/-! # Filtration of the rows of the lifted cyclic action -/

noncomputable section

open ValuativeRel Polynomial IsLocalRing
open scoped BigOperators

namespace Langlands.BushnellKutzko.CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (C : LatticeChain 𝒪[F] F V)

theorem uniformizerUnit_shifts : Shifts C C.period (scalarEndUnit (LatticeChain.uniformizerAsUnit hϖ)) := by
  have h := Shifts.of_stabilizer (C.uniformizerStabilizer hϖ)
  rw [C.uniformizerStabilizer_shift hϖ] at h
  exact h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem scalarEndUnit_zpow_coe (π : Fˣ) (t : ℤ) :
    (↑((scalarEndUnit (V := V) π) ^ t) : Module.End F V) = algebraMap F _ ((π : F) ^ t) := by
  rw [← map_zpow (Units.map (algebraMap F (Module.End F V)).toMonoidHom), Units.coe_map,
    Units.val_zpow_eq_zpow_val]
  rfl

private theorem rowDegree_injective {h g e : ℕ} (he : e = h * g) (hg : 0 < g) (t : Fin h → ℤ) :
    Function.Injective (fun m : Fin h => (m : ℤ) * g + (e : ℤ) * t m) := by
  intro i j hij
  have he' : (e : ℤ) = (h : ℤ) * (g : ℤ) := by exact_mod_cast he
  have heq : ((i : ℤ) + (h : ℤ) * t i) * g = ((j : ℤ) + (h : ℤ) * t j) * g := by
    rw [he'] at hij
    linear_combination hij
  have heq' := mul_right_cancel₀ (show (g : ℤ) ≠ 0 by exact_mod_cast hg.ne') heq
  have hmod (m : Fin h) : ((m : ℤ) + (h : ℤ) * t m) % (h : ℤ) = (m : ℤ) := by
    rw [Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul, Int.zero_emod, add_zero, Int.emod_emod]
    exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast m.isLt)
  have hval := (hmod i).symm.trans ((congrArg (fun a : ℤ => a % (h : ℤ)) heq').trans (hmod j))
  exact Fin.ext (by exact_mod_cast hval)

section Rows

variable {g h : ℕ} (P : (𝒪[F])[X]) {a : ℤ}
  (M : CyclicAlgebra (P.map (algebraMap 𝒪[F] F)) h P.natDegree (LatticeChain.uniformizerAsUnit hϖ) a)
  {z τ : Module.End F V} (B : CyclicBasis C g h P.natDegree z τ)

local notation "U'" => B.actionU M
local notation "T'" => B.actionT M
local notation "D" => C.endFiltration

/-- Separate the expansion in the rectangular power basis into rows by the shift exponent. -/
def evaluatedRow (w : M.A) (m : Fin h) : Module.End F V :=
  (T' : Module.End F V) ^ (m : ℕ) *
    ∑ l : Fin P.natDegree, M.basis.repr w (m, l) • (U' : Module.End F V) ^ (l : ℕ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem action_eq_sum_rows (w : M.A) : B.action M w = ∑ m, evaluatedRow hϖ C P M B w m := by
  conv_lhs => rw [← M.basis.sum_repr w]
  rw [map_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro m _
  rw [evaluatedRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul, M.basis_apply, map_mul, map_pow, map_pow, Algebra.mul_smul_comm]
  rfl

set_option maxHeartbeats 500000 in
private theorem row_factor (hP : P.Monic) (hp : Irreducible (P.map (residue 𝒪[F])))
    (hu : Shifts C 0 U') (ht : Shifts C g T') {x : Module.End F V}
    (hux : (U' : Module.End F V) ∈ leadingCommutant C x 0)
    (htx : (T' : Module.End F V) ∈ leadingCommutant C x g) (w : M.A) (m : Fin h)
    (hm : evaluatedRow hϖ C P M B w m ≠ 0) :
    ∃ (t : ℤ) (v : (Module.End F V)ˣ), (v : Module.End F V) = evaluatedRow hϖ C P M B w m ∧
      Shifts C ((m : ℤ) * g + (C.period : ℤ) * t) v ∧
      (v : Module.End F V) ∈ leadingCommutant C x ((m : ℤ) * g + (C.period : ℤ) * t) := by
  have hcoeff : ∃ l, M.basis.repr w (m, l) ≠ 0 := by
    by_contra! hz
    exact hm (by simp [evaluatedRow, hz])
  obtain ⟨t, r, hr, hprim⟩ := exists_primitive_coeffs hϖ _ hcoeff
  let U₀ : C.order := ⟨U', C.mem_order_iff_mem_endFiltration.mpr hu.1⟩
  have hQ : aeval U₀.val (P.map (algebraMap 𝒪[F] F)) ∈ D 1 := by
    change aeval (U' : Module.End F V) _ ∈ _
    rw [B.actionU_eval_zero M]
    exact zero_mem _
  obtain ⟨U, hU, hUs⟩ := exists_unit_of_primitive_powerSum C P U₀ hQ hP hp r hprim
  have hU' : (U : Module.End F V) = ∑ l : Fin P.natDegree,
      (r l : F) • (U' : Module.End F V) ^ (l : ℕ) := by
    rw [hU, integralPowerSum_val]
  let π := scalarEndUnit (V := V) (LatticeChain.uniformizerAsUnit hϖ)
  have hπ := (uniformizerUnit_shifts hϖ C).zpow t
  let v := T' ^ (m : ℕ) * π ^ t * U
  have hv : (v : Module.End F V) = evaluatedRow hϖ C P M B w m := by
    change (T' : Module.End F V) ^ (m : ℕ) * ↑(π ^ t) * (U : Module.End F V) = _
    rw [evaluatedRow, hU', mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [hr l, scalarEndUnit_zpow_coe]
    change algebraMap F _ ((ϖ : F) ^ t) * ((r l : F) • (U' : Module.End F V) ^ (l : ℕ)) = _
    rw [← Algebra.smul_def, smul_smul]
  have hvs : Shifts C ((m : ℤ) * g + t * (C.period : ℤ)) v := by
    simpa only [add_zero] using ((ht.pow (m : ℕ)).mul hπ).mul hUs
  have hπx : (↑(π ^ t) : Module.End F V) ∈ leadingCommutant C x (t * (C.period : ℤ)) := by
    rw [scalarEndUnit_zpow_coe]
    exact LeadingCommutant.of_commute _ (Algebra.commutes _ _)
  have hUc : (U : Module.End F V) ∈ leadingCommutant C x 0 := by
    rw [hU']
    apply Submodule.sum_mem
    intro l _
    have hl := LeadingCommutant.pow_mem hu hux (l : ℕ)
    rw [mul_zero] at hl
    exact (leadingCommutant C x 0).smul_mem (r l) hl
  have hTx := LeadingCommutant.pow_mem ht htx (m : ℕ)
  have hvc := LeadingCommutant.mul_mem
    (C.mul_mem_endFiltration (ht.pow (m : ℕ)).1 hπ.1) hUs.1
    (LeadingCommutant.mul_mem (ht.pow (m : ℕ)).1 hπ.1 hTx hπx) hUc
  exact ⟨t, v, hv, by simpa only [mul_comm (C.period : ℤ) t] using hvs,
    by simpa only [v, π, Units.val_mul, add_zero, mul_comm (C.period : ℤ) t] using hvc⟩

set_option maxHeartbeats 500000 in
/-- Every nonzero image of the cyclic action is a shifting unit. If the two transported
roots commute with `x` one step beyond their degrees, the same holds for this unit at
its shift. The finite rows have distinct degrees modulo the period. -/
theorem exists_shifts_of_cyclicAction (hP : P.Monic) (hp : Irreducible (P.map (residue 𝒪[F])))
    (he : C.period = h * g) (hg : 0 < g) (hu : Shifts C 0 U') (ht : Shifts C g T')
    {x : Module.End F V} (hux : (U' : Module.End F V) ∈ leadingCommutant C x 0)
    (htx : (T' : Module.End F V) ∈ leadingCommutant C x g) (w : M.A) (hw : B.action M w ≠ 0) :
    ∃ (j : ℤ) (v : (Module.End F V)ˣ), (v : Module.End F V) = B.action M w ∧ Shifts C j v ∧
      (v : Module.End F V) ∈ leadingCommutant C x j := by
  classical
  let r := evaluatedRow hϖ C P M B w
  let s := Finset.univ.filter (fun m => r m ≠ 0)
  have hsum : B.action M w = ∑ m ∈ s, r m := by
    rw [action_eq_sum_rows]
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (by simp [s])
  have hs : s.Nonempty := by
    by_contra! hs
    exact hw (by rw [hsum, hs, Finset.sum_empty])
  have hrow (m : Fin h) : ∃ t : ℤ, r m ≠ 0 → ∃ v : (Module.End F V)ˣ,
      (v : Module.End F V) = r m ∧ Shifts C ((m : ℤ) * g + (C.period : ℤ) * t) v ∧
        (v : Module.End F V) ∈ leadingCommutant C x ((m : ℤ) * g + (C.period : ℤ) * t) := by
    by_cases hm : r m ≠ 0
    · obtain ⟨t, v, hv, hvs, hvc⟩ := row_factor hϖ C P M B hP hp hu ht hux htx w m hm
      exact ⟨t, fun _ => ⟨v, hv, hvs, hvc⟩⟩
    · exact ⟨0, fun h => (hm h).elim⟩
  choose t ht' using hrow
  let deg (m : Fin h) : ℤ := (m : ℤ) * g + (C.period : ℤ) * t m
  have hdeg : Function.Injective deg := rowDegree_injective he hg t
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image s deg hs
  have hnz (n : Fin h) (hn : n ∈ s) : r n ≠ 0 := (Finset.mem_filter.mp hn).2
  obtain ⟨v₀, hv₀, hvs₀, hvc₀⟩ := ht' m (hnz m hm)
  have hhi (n : Fin h) (hn : n ∈ s.erase m) : deg m < deg n :=
    lt_of_le_of_ne (hmin n (Finset.mem_of_mem_erase hn)) (fun h =>
      (Finset.ne_of_mem_erase hn) (hdeg h).symm)
  have hrest : (∑ n ∈ s.erase m, r n) ∈ D (deg m + 1) := by
    apply Submodule.sum_mem
    intro n hn
    obtain ⟨v, hv, hvs, -⟩ := ht' n (hnz n (Finset.mem_of_mem_erase hn))
    rw [← hv]
    exact C.endFiltration_antitone (show deg m + 1 ≤ deg n by have := hhi n hn; omega) hvs.1
  have hsplit : B.action M w = (v₀ : Module.End F V) + ∑ n ∈ s.erase m, r n := by
    rw [hsum, ← Finset.sum_erase_add _ _ hm, hv₀, add_comm]
  have hsym : SymbolEq C (deg m) (B.action M w) (v₀ : Module.End F V) := by
    rw [hsplit]
    exact SymbolEq.lowerDepth hvs₀.1 hrest (by omega)
  obtain ⟨v, hv, hvs⟩ := exists_unit_of_symbolEq_self C hvs₀ hsym
  refine ⟨deg m, v, hv, hvs, ?_⟩
  rw [hv, hsum]
  apply Submodule.sum_mem
  intro n hn
  obtain ⟨v, hv, -, hvc⟩ := ht' n (hnz n hn)
  rw [← hv]
  exact LeadingCommutant.antitone (hmin n hn) hvc

end Rows

end Langlands.BushnellKutzko.CriticalDerived
