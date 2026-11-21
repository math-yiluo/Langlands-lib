import Langlands.BushnellKutzko.CriticalDerivedCyclicAction

/-! # The two lifted operators have the original leading symbols -/

noncomputable section

open ValuativeRel Polynomial
open scoped BigOperators

namespace Langlands.BushnellKutzko.CriticalDerived

universe uF uV

private theorem aeval_monic_eq_pow_add_sum {F : Type*} [Field F] {A : Type*}
    [Ring A] [Algebra F A] {Q : F[X]} (hQ : Q.Monic) {f : ℕ} (hf : Q.natDegree = f) (x : A) :
    aeval x Q = x ^ f + ∑ l : Fin f, Q.coeff (l : ℕ) • x ^ (l : ℕ) := by
  subst f
  rw [aeval_def, eval₂_eq_sum_range, Finset.sum_range_succ, hQ.coeff_natDegree,
    map_one, one_mul, add_comm, ← Fin.sum_univ_eq_sum_range]
  simp only [Algebra.smul_def]

private theorem apply_pow_apply_of_commute {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {z τ : Module.End F V} (hc : Commute z τ) (m l : ℕ) (v : V) :
    z ((τ ^ m) ((z ^ l) v)) = (τ ^ m) ((z ^ (l + 1)) v) := by
  rw [← Module.End.mul_apply, (hc.pow_right m).eq, Module.End.mul_apply, pow_succ', Module.End.mul_apply]

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {C : LatticeChain 𝒪[F] F V} {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
  {Q : F[X]} {g h f : ℕ} {π : Fˣ} {a : ℤ} (M : CyclicAlgebra Q h f π a)
  {z τ : (Module.End F V)ˣ} (B : CyclicBasis C g h f (z : Module.End F V) (τ : Module.End F V))

local notation "L" => C.lattice
local notation "D" => C.endFiltration
local notation "U'" => B.actionU M
local notation "T'" => B.actionT M

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem generator_mem (hh : 0 < h) (hf : 0 < f) (i : Σ i : Fin g, Fin (B.count i)) :
    B.generators i.1 i.2 ∈ L (i.1 : ℤ) := by
  have hd := (B.depth (i, ⟨0, hh⟩, ⟨0, hf⟩)).1
  simpa only [B.basis_apply, pow_zero, Module.End.one_apply, cyclicWeight, Fin.val_mk,
    Nat.cast_zero, zero_mul, add_zero] using hd

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem short_iterates (hh : 0 < h) (hf : 0 < f) (t : CyclicIndex B.count h f) :
    ((T' : Module.End F V) ^ (t.2.1 : ℕ))
        (((U' : Module.End F V) ^ (t.2.2 : ℕ)) (B.generators t.1.1 t.1.2)) =
      ((τ : Module.End F V) ^ (t.2.1 : ℕ))
        (((z : Module.End F V) ^ (t.2.2 : ℕ)) (B.generators t.1.1 t.1.2)) :=
  (B.action_basis M hh hf t).symm.trans (B.basis_apply t)

private theorem shifts_of_symbol_of_shifts {b c : (Module.End F V)ˣ} {j : ℤ}
    (hc : Shifts C j c) (hbc : SymbolEq C j (b : Module.End F V) c) : Shifts C j b := by
  obtain ⟨b', hb', h⟩ := exists_unit_of_symbolEq_self C hc hbc
  rwa [show b' = b from Units.ext hb'] at h

set_option maxHeartbeats 500000 in
include hϖ in
/-- The transported residual root has the same degree-zero symbol as `z`. At the last
residual power, the difference between the two actions is a multiple of `Q(z)` on a
layer generator. -/
theorem actionU_symbol (hQ : Q.Monic) (hfdeg : Q.natDegree = f) (hh : 0 < h) (hf : 0 < f)
    (hc : Commute z τ) (ht : Shifts C g τ) (hz : Shifts C 0 z)
    (hQz : aeval (z : Module.End F V) Q ∈ D 1) :
    SymbolEq C 0 (U' : Module.End F V) z := by
  have hdiff : (U' : Module.End F V) - (z : Module.End F V) ∈ D 1 := by
    rw [mem_endFiltration_iff_splittingBasis hϖ C B.basis B.splits cyclicWeight B.depth]
    intro t
    let m : ℕ := t.2.1
    let l : ℕ := t.2.2
    let v := B.generators t.1.1 t.1.2
    simp only [LinearMap.sub_apply]
    have hU : (U' : Module.End F V) (B.basis t) =
        ((T' : Module.End F V) ^ m) (((U' : Module.End F V) ^ (l + 1)) v) := by
      rw [B.action_basis M hh hf]
      exact apply_pow_apply_of_commute
        (by exact (B.action_commutes M).symm.map (Units.coeHom (Module.End F V))) m l v
    have hz' : (z : Module.End F V) (B.basis t) =
        ((τ : Module.End F V) ^ m) (((z : Module.End F V) ^ (l + 1)) v) := by
      rw [B.basis_apply]
      exact apply_pow_apply_of_commute (hc.map (Units.coeHom (Module.End F V))) m l v
    rw [hU, hz']
    by_cases hl : l + 1 < f
    · rw [short_iterates M B hh hf (t.1, t.2.1, ⟨l + 1, hl⟩), sub_self]
      exact zero_mem _
    · have hlf : l + 1 = f := by have := t.2.2.isLt; dsimp [l] at *; omega
      rw [hlf]
      let s (x : Module.End F V) := ∑ j : Fin f, Q.coeff (j : ℕ) • x ^ (j : ℕ)
      have hsum : ((T' : Module.End F V) ^ m) (s U' v) = ((τ : Module.End F V) ^ m) (s z v) := by
        simp only [s, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro j _
        rw [short_iterates M B hh hf (t.1, t.2.1, j)]
      have hu₀ := B.actionU_eval_zero M
      rw [aeval_monic_eq_pow_add_sum hQ hfdeg] at hu₀
      have hu₁ : (U' : Module.End F V) ^ f = -s U' := add_eq_zero_iff_eq_neg.mp hu₀
      have heq : ((T' : Module.End F V) ^ m) (((U' : Module.End F V) ^ f) v) -
          ((τ : Module.End F V) ^ m) (((z : Module.End F V) ^ f) v) =
          -((τ : Module.End F V) ^ m) ((aeval (z : Module.End F V) Q) v) := by
        rw [hu₁, LinearMap.neg_apply, map_neg, hsum, aeval_monic_eq_pow_add_sum hQ hfdeg,
          LinearMap.add_apply, map_add]
        change -((τ : Module.End F V) ^ m) (s z v) - _ =
          -(((τ : Module.End F V) ^ m) (((z : Module.End F V) ^ f) v) + ((τ : Module.End F V) ^ m) (s z v))
        abel
      rw [heq]
      exact neg_mem (C.mul_mem_endFiltration (ht.pow m).1 hQz _ v (generator_mem B hh hf t.1))
  exact ⟨by simpa only [sub_add_cancel] using add_mem (C.endFiltration_antitone (by omega) hdiff) hz.1,
    hz.1, hdiff⟩

set_option maxHeartbeats 450000 in
include hϖ in
/-- The transported shift root has the same symbol in degree `g` as `τ`. At the last
shift power, compare the two carry relations using the already matched residual roots. -/
theorem actionT_symbol (hh : 0 < h) (hf : 0 < f) (he : C.period = h * g)
    (ht : Shifts C g τ) (hz : Shifts C 0 z) (hπ : Shifts C C.period (scalarEndUnit π))
    (hτh : τ ^ h = scalarEndUnit π * z ^ a) (hu : SymbolEq C 0 (U' : Module.End F V) z) :
    SymbolEq C g (T' : Module.End F V) τ := by
  have hu' := shifts_of_symbol_of_shifts hz hu
  have hcarry := (SymbolEq.refl hπ.1).mul (hu.zpow hu' hz a)
  rw [mul_zero, add_zero] at hcarry
  have hdiff : (T' : Module.End F V) - (τ : Module.End F V) ∈ D ((g : ℤ) + 1) := by
    rw [mem_endFiltration_iff_splittingBasis hϖ C B.basis B.splits cyclicWeight B.depth]
    intro t
    let m : ℕ := t.2.1
    let l : ℕ := t.2.2
    let v := B.generators t.1.1 t.1.2
    simp only [LinearMap.sub_apply]
    have hT : (T' : Module.End F V) (B.basis t) =
        ((T' : Module.End F V) ^ (m + 1)) (((U' : Module.End F V) ^ l) v) := by
      rw [B.action_basis M hh hf, pow_succ', Module.End.mul_apply]
    have hτ : (τ : Module.End F V) (B.basis t) =
        ((τ : Module.End F V) ^ (m + 1)) (((z : Module.End F V) ^ l) v) := by
      rw [B.basis_apply, pow_succ', Module.End.mul_apply]
    rw [hT, hτ]
    by_cases hm : m + 1 < h
    · rw [short_iterates M B hh hf (t.1, ⟨m + 1, hm⟩, t.2.2), sub_self]
      exact zero_mem _
    · have hmh : m + 1 = h := by have := t.2.1.isLt; dsimp [m] at *; omega
      have hshort := short_iterates M B hh hf (t.1, ⟨0, hh⟩, t.2.2)
      simp only [pow_zero, Module.End.one_apply] at hshort
      rw [hmh, hshort, ← Units.val_pow_eq_pow_val T' h, B.actionT_carry M,
        ← Units.val_pow_eq_pow_val τ h, hτh]
      have hw : ((z : Module.End F V) ^ l) v ∈ L (t.1.1 : ℤ) := by
        simpa only [mul_zero, add_zero, Units.val_pow_eq_pow_val] using
          (hz.pow l).1 _ v (generator_mem B hh hf t.1)
      have hwt : cyclicWeight t + ((g : ℤ) + 1) = (t.1.1 : ℤ) + ((C.period : ℤ) + 1) := by
        change (t.1.1 : ℤ) + (m : ℤ) * g + ((g : ℤ) + 1) = _
        have hk := congrArg (fun n : ℕ => (n : ℤ) * (g : ℤ)) hmh
        push_cast at hk
        rw [he, Nat.cast_mul, ← hk]
        ring
      rw [hwt]
      exact hcarry.2.2 _ _ hw
  exact ⟨by simpa only [sub_add_cancel] using add_mem (C.endFiltration_antitone (by omega) hdiff) ht.1,
    ht.1, hdiff⟩

theorem actionU_shifts (hz : Shifts C 0 z) (hu : SymbolEq C 0 (U' : Module.End F V) z) :
    Shifts C 0 U' := shifts_of_symbol_of_shifts hz hu

theorem actionT_shifts (ht : Shifts C g τ) (hs : SymbolEq C g (T' : Module.End F V) τ) :
    Shifts C g T' := shifts_of_symbol_of_shifts ht hs

end Langlands.BushnellKutzko.CriticalDerived
