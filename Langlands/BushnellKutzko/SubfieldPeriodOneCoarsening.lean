import Langlands.BushnellKutzko.SubfieldOrderProof
import Langlands.BushnellKutzko.SubfieldPeriodOneCoarseningStatement
import Langlands.BushnellKutzko.SubfieldValuationShifts

/-! # Coarsening to an order of relative period one -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uF uE uV

section Coarsening

variable {O : Type uO} [CommRing O] {F : Type uF} [Field F] [Algebra O F]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]
  (L : LatticeChain O F V)

/-- Keeping every `d`-th lattice of a chain whose period is `d * e` gives
a chain of period `e`. -/
def coarsen (d e : ℕ) (hd : 0 < d) (he : L.period = d * e) : LatticeChain O F V where
  lattice i := L.lattice (i * d)
  isLattice i := L.isLattice (i * d)
  lattice_succ_lt i := L.strictAnti (by
    rw [add_mul, one_mul]
    exact lt_add_of_pos_right _ (by exact_mod_cast hd))
  exists_period := by
    have he' : 0 < e := Nat.pos_of_ne_zero fun h =>
      L.period_pos.ne' (he.trans (by simp [h]))
    refine ⟨e, he', fun i => ?_⟩
    rw [add_mul, ← Nat.cast_mul, mul_comm e d, ← he, L.lattice_add_period]

variable {d e : ℕ} (hd : 0 < d) (he : L.period = d * e)

theorem period_coarsen : (L.coarsen d e hd he).period = e := by
  symm
  apply (L.coarsen d e hd he).period_unique
  intro i
  change L.lattice ((i + e) * d) = Ring.jacobson O • L.lattice (i * d)
  rw [add_mul, ← Nat.cast_mul, mul_comm e d, ← he, L.lattice_add_period]

/-- Restriction to the retained lattices enlarges the order. -/
theorem order_le_order_coarsen : L.order ≤ (L.coarsen d e hd he).order := by
  intro x hx
  exact (mem_order _).mpr fun i v hv => (L.mem_order.mp hx) (i * d) v hv

/-- A map that lowers the coarser chain by one step lowers the original chain
by one step. -/
theorem coarsen_endFiltration_one_le :
    (L.coarsen d e hd he).endFiltration 1 ≤ L.endFiltration 1 := by
  intro x hx i v hv
  let j := i / (d : ℤ)
  have hd' : 0 < (d : ℤ) := by exact_mod_cast hd
  have h₀ : 0 ≤ i % (d : ℤ) := Int.emod_nonneg _ hd'.ne'
  have h₁ : i % (d : ℤ) < d := Int.emod_lt_of_pos _ hd'
  have hi : i % (d : ℤ) + (d : ℤ) * j = i := Int.emod_add_mul_ediv _ _
  have hle : j * (d : ℤ) ≤ i := by
    rw [mul_comm]
    omega
  have hge : i + 1 ≤ (j + 1) * (d : ℤ) := by
    rw [add_mul, one_mul, mul_comm j]
    omega
  exact L.antitone hge (hx j v (L.antitone hle hv))

/-- The unit group enlarges under coarsening, and its first congruence subgroup
is contained in the original first congruence subgroup. -/
theorem unitFiltration_coarsen_bounds :
    L.unitFiltration 0 ≤ (L.coarsen d e hd he).unitFiltration 0 ∧
      (L.coarsen d e hd he).unitFiltration 1 ≤ L.unitFiltration 1 := by
  constructor
  · intro g hg
    exact (mem_unitFiltration_zero _).mpr
      ⟨L.order_le_order_coarsen hd he hg.1, L.order_le_order_coarsen hd he hg.2.1⟩
  · intro g hg
    have hx := L.coarsen_endFiltration_one_le hd he hg.2.2
    obtain ⟨u, hu, heq⟩ := L.exists_mem_unitFiltration (n := 1) le_rfl hx
    have hug : u = g := Units.ext (by rw [heq]; abel)
    exact hug ▸ hu

end Coarsening

/-- In the construction of BK93 (5.1.12), the larger relative order can be
obtained by retaining the translates of the zeroth lattice by the extension
uniformizer. The new relative chain has period one. -/
theorem subfieldPeriodOneCoarsening : SubfieldPeriodOneCoarseningStatement.{uF, uE, uV} := by
  intro F _ _ _ _ E _ _ V _ _ _ _ L hE
  let _ := L.finiteDimensional_subfield E
  let _ := subfieldIntegers_isDiscreteValuationRing F E
  let _ := subfieldIntegers_isFractionRing F E
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  let π := subfieldIntegerUnit E hϖ.ne_zero
  let r := (L.fieldShift E hE π).toAdd
  let d := r.toNat
  let e := subfieldRamificationIndex F E
  have hr : 0 < r := L.fieldShift_uniformizer_pos E hE hϖ
  have hd : (d : ℤ) = r := Int.toNat_of_nonneg hr.le
  have hd' : 0 < d := by
    have h : 0 < (d : ℤ) := hd.symm ▸ hr
    exact_mod_cast h
  have hperiod : L.period = d * e := by
    have h : r * (e : ℤ) = (L.period : ℤ) := L.fieldShift_uniformizer_mul_ramification E hE hϖ
    rw [← hd] at h
    exact_mod_cast h.symm
  let M := L.coarsen d e hd' hperiod
  have hM (a : Eˣ) : subfieldUnits F E V a ∈ M.stabilizer := by
    obtain ⟨k, u, hu⟩ := subfieldUnit_factorization E hϖ a
    have ha : L.stabilizerValuation ⟨subfieldUnits F E V a, hE a⟩ = r * k :=
      L.fieldShift_eq_mul_of_factorization E hE hϖ.ne_zero hu
    intro i
    refine ⟨i + k, ?_⟩
    change (L.lattice (i * d)).map
      (((subfieldUnits F E V a : (Module.End F V)ˣ) : Module.End F V).restrictScalars 𝒪[F]) =
      L.lattice ((i + k) * d)
    rw [show (L.lattice (i * d)).map
        (((subfieldUnits F E V a : (Module.End F V)ˣ) : Module.End F V).restrictScalars 𝒪[F]) =
        L.lattice (i * d + L.stabilizerValuation ⟨subfieldUnits F E V a, hE a⟩)
      from L.map_lattice_stabilizer ⟨_, hE a⟩ (i * d), ha, ← hd, add_mul, mul_comm (d : ℤ) k]
  have hMperiod : M.period = e := L.period_coarsen hd' hperiod
  obtain ⟨C, hC, -, -, -, -, hCperiod⟩ := subfieldOrder F V E M hM
  have he : e ≠ 0 := (hMperiod ▸ M.period_pos).ne'
  have hone : C.period = 1 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he)
    (by rw [← hCperiod, ← hMperiod, mul_one])
  have h0 : M.lattice 0 = L.lattice 0 := by change L.lattice (0 * d) = _; rw [zero_mul]
  exact ⟨M, hM, h0, hMperiod, (L.unitFiltration_coarsen_bounds hd' hperiod).1,
    (L.unitFiltration_coarsen_bounds hd' hperiod).2, C, hone, hC⟩

end Langlands.BushnellKutzko.LatticeChain
