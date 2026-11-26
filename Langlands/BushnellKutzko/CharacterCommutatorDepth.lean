import Langlands.BushnellKutzko.AdjointLatticeLifting
import Langlands.BushnellKutzko.RefinementCore
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Langlands.BushnellKutzko.SimpleCharacters

/-! # Adjoint congruence subgroups and the trace of a commutator -/

noncomputable section

open ValuativeRel
open scoped commutatorElement

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "O" => 𝒪[F]
local notation "tr" => LinearMap.trace F V

/-- At a positive index, membership in the congruence subgroup is equivalent
to the filtration condition on the difference from one. -/
theorem LatticeChain.mem_unitFiltration_of_sub_one_iff (L : LatticeChain O F V)
    {k : ℕ} (hk : 1 ≤ k) {g : G} :
    g ∈ L.unitFiltration k ↔ (g : A) - 1 ∈ L.endFiltration k := by
  refine ⟨fun h => h.2.2, fun h => ?_⟩
  obtain ⟨u, hu, hval⟩ := L.exists_mem_unitFiltration hk h
  have hug : u = g := Units.ext (by
    rw [hval]
    abel)
  exact hug ▸ hu

omit [ValuativeRel F] in
private theorem adjointMap_mul_apply (b x y : A) :
    adjointMap F b (x * y) = adjointMap F b x * y + x * adjointMap F b y := by
  change b * (x * y) - (x * y) * b = (b * x - x * b) * y + x * (b * y - y * b)
  noncomm_ring

omit [ValuativeRel F] in
private theorem adjointMap_sub_one_apply (b x : A) :
    adjointMap F b (x - 1) = adjointMap F b x := by
  rw [map_sub, show adjointMap F b 1 = 0 by simp [adjointMap], sub_zero]

omit [ValuativeRel F] in
private theorem adjointMap_inv_apply (b : A) (u : G) :
    adjointMap F b (↑u⁻¹ : A) = -((↑u⁻¹ : A) * adjointMap F b (u : A) * (↑u⁻¹ : A)) := by
  change b * (↑u⁻¹ : A) - (↑u⁻¹ : A) * b =
    -((↑u⁻¹ : A) * (b * (u : A) - (u : A) * b) * (↑u⁻¹ : A))
  rw [mul_sub, sub_mul, ← mul_assoc (↑u⁻¹ : A) b (u : A), ← mul_assoc (↑u⁻¹ : A) (u : A) b,
    mul_assoc ((↑u⁻¹ : A) * b), Units.mul_inv, mul_one, Units.inv_mul, one_mul, neg_sub]

/-- A mixed adjoint congruence subgroup at positive depth. -/
def mixedAdjointUnitGroup (L : LatticeChain O F V) (b : A) (k : ℕ) (j : ℤ)
    (hk : 1 ≤ k) : Subgroup G where
  carrier := {g | (g : A) - 1 ∈ mixedAdjointLattice L b k j}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change (x : A) - 1 ∈ mixedAdjointLattice L b k j at hx
    change (y : A) - 1 ∈ mixedAdjointLattice L b k j at hy
    have hxU := (L.mem_unitFiltration_of_sub_one_iff hk).mpr hx.1
    have hyU := (L.mem_unitFiltration_of_sub_one_iff hk).mpr hy.1
    refine ⟨(mul_mem hxU hyU).2.2, ?_⟩
    change adjointMap F b ((↑(x * y) : A) - 1) ∈ L.endFiltration (k + j)
    rw [adjointMap_sub_one_apply, Units.val_mul, adjointMap_mul_apply]
    have hx' : adjointMap F b (x : A) ∈ L.endFiltration (k + j) :=
      (adjointMap_sub_one_apply b (x : A)) ▸ hx.2
    have hy' : adjointMap F b (y : A) ∈ L.endFiltration (k + j) :=
      (adjointMap_sub_one_apply b (y : A)) ▸ hy.2
    exact add_mem (by simpa only [add_zero] using L.mul_mem_endFiltration hx' hyU.1)
      (by simpa only [zero_add] using L.mul_mem_endFiltration hxU.1 hy')
  inv_mem' := by
    intro x hx
    change (x : A) - 1 ∈ mixedAdjointLattice L b k j at hx
    have hxU := (L.mem_unitFiltration_of_sub_one_iff hk).mpr hx.1
    have hxi : x⁻¹ ∈ L.unitFiltration k := inv_mem hxU
    refine ⟨hxi.2.2, ?_⟩
    change adjointMap F b ((↑x⁻¹ : A) - 1) ∈ L.endFiltration (k + j)
    rw [adjointMap_sub_one_apply, adjointMap_inv_apply]
    have hx' : adjointMap F b (x : A) ∈ L.endFiltration (k + j) :=
      (adjointMap_sub_one_apply b (x : A)) ▸ hx.2
    exact neg_mem (by simpa only [zero_add, add_zero] using
      L.mul_mem_endFiltration (L.mul_mem_endFiltration hxi.1 hx') hxi.1)

@[simp]
theorem mem_mixedAdjointUnitGroup_iff {L : LatticeChain O F V} {b : A} {k : ℕ} {j : ℤ}
    {hk : 1 ≤ k} {g : G} :
    g ∈ mixedAdjointUnitGroup L b k j hk ↔ (g : A) - 1 ∈ mixedAdjointLattice L b k j := Iff.rfl

/-- A mixed adjoint congruence implies the corresponding congruence for the
conjugate of the parameter. -/
theorem conjugation_sub_mem_of_mem_mixedAdjointUnitGroup {L : LatticeChain O F V}
    {b : A} {k : ℕ} {j : ℤ} {hk : 1 ≤ k}
    {g : G} (hg : g ∈ mixedAdjointUnitGroup L b k j hk) :
    (↑g⁻¹ : A) * b * (g : A) - b ∈ L.endFiltration (k + j) := by
  obtain ⟨hP, ha⟩ := mem_mixedAdjointUnitGroup_iff.mp hg
  change adjointMap F b ((g : A) - 1) ∈ L.endFiltration (k + j) at ha
  rw [adjointMap_sub_one_apply] at ha
  have hInv : (↑g⁻¹ : A) ∈ L.order := (L.mem_unitFiltration_of_sub_one_iff hk).mpr hP |>.2.1
  have h := L.mul_mem_endFiltration hInv ha
  change (↑g⁻¹ : A) * (b * (g : A) - (g : A) * b) ∈ L.endFiltration (0 + (k + j)) at h
  simpa only [mul_sub, ← mul_assoc, Units.inv_mul, one_mul, zero_add] using h

omit [ValuativeRel F] in
/-- The difference of a commutator from one is the additive commutator of the
two differences, multiplied on the right by the inverse units. -/
theorem commutatorElement_sub_one (x y : G) :
    (↑⁅x, y⁆ : A) - 1 =
      (((x : A) - 1) * ((y : A) - 1) - ((y : A) - 1) * ((x : A) - 1)) *
        (↑x⁻¹ : A) * (↑y⁻¹ : A) := by
  have h : ((x : A) - 1) * ((y : A) - 1) - ((y : A) - 1) * ((x : A) - 1) =
      (x : A) * (y : A) - (y : A) * (x : A) := by noncomm_ring
  rw [h, sub_mul, sub_mul, mul_assoc (y : A) (x : A), Units.mul_inv, mul_one, Units.mul_inv]
  rfl

/-- The additive character calculation of BK93 (3.2.9). The error in
replacing the group commutator by the conjugation difference disappears
once `k + 2 l` is beyond the negative depth of the coefficient. -/
theorem elementCharacter_commutator_of_depth [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (L : LatticeChain O F V) (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {b : A} {r : ℤ} (hb : b ∈ L.endFiltration (-r))
    {k l : ℕ} (hkl : r + 1 ≤ (k : ℤ) + 2 * (l : ℤ)) {x y : G}
    (hx : x ∈ L.unitFiltration k) (hy : y ∈ L.unitFiltration l) :
    elementCharacter (traceCharacter ψF) b ⁅x, y⁆ =
      elementCharacter (traceCharacter ψF) ((↑x⁻¹ : A) * b * (x : A) - b) y := by
  let d : A := (x : A) * ((y : A) - 1) * (↑x⁻¹ : A) - ((y : A) - 1)
  have hdeq : d = ((x : A) * (y : A) - (y : A) * (x : A)) * (↑x⁻¹ : A) := by
    dsimp only [d]
    rw [mul_sub, mul_one, sub_mul, sub_mul, mul_assoc (y : A) (x : A), Units.mul_inv, mul_one]
    abel
  have hd : d ∈ L.endFiltration ((k : ℤ) + (l : ℤ)) := by
    rw [hdeq]
    have hc : (x : A) * (y : A) - (y : A) * (x : A) ∈ L.endFiltration ((k : ℤ) + l) := by
      convert commutator_mem_endFiltration L hx.2.2 hy.2.2 using 1
      noncomm_ring
    simpa only [add_zero] using L.mul_mem_endFiltration hc hx.2.1
  have hc : (↑⁅x, y⁆ : A) - 1 = d * (↑y⁻¹ : A) := by
    rw [commutatorElement_sub_one, hdeq]
    congr 2
    noncomm_ring
  have he : (↑⁅x, y⁆ : A) - 1 - d = -(d * ((y : A) - 1) * (↑y⁻¹ : A)) := by
    have hmul : d * ((y : A) - 1) * (↑y⁻¹ : A) = d - d * (↑y⁻¹ : A) := by
      calc
        d * ((y : A) - 1) * (↑y⁻¹ : A) = (d * (y : A) - d) * (↑y⁻¹ : A) := by
          rw [mul_sub, mul_one]
        _ = _ := by rw [sub_mul, mul_assoc d (y : A), Units.mul_inv, mul_one]
    rw [hc, hmul, neg_sub]
  have htriv : traceCharacter ψF (b * ((↑⁅x, y⁆ : A) - 1 - d)) = 1 := by
    have he' : (↑⁅x, y⁆ : A) - 1 - d ∈ L.endFiltration ((k : ℤ) + 2 * (l : ℤ)) := by
      rw [he]
      apply neg_mem
      rw [show (k : ℤ) + 2 * (l : ℤ) = ((k : ℤ) + l) + l + 0 by omega]
      exact L.mul_mem_endFiltration (L.mul_mem_endFiltration hd hy.2.2) hy.2.1
    have hb' := L.endFiltration_antitone (by omega : 1 ≤ -r + ((k : ℤ) + 2 * (l : ℤ)))
      (L.mul_mem_endFiltration hb he')
    obtain ⟨s, hs, htrace⟩ := L.trace_mem_maximalIdealInField hb'
    rw [traceCharacter_apply, ← htrace]
    exact hψ.1 s hs
  have ht : tr (b * d) = tr (((↑x⁻¹ : A) * b * (x : A) - b) * ((y : A) - 1)) := by
    dsimp only [d]
    rw [mul_sub, sub_mul, map_sub, map_sub]
    congr 1
    calc
      tr (b * ((x : A) * ((y : A) - 1) * (↑x⁻¹ : A))) =
          tr ((b * (x : A)) * ((y : A) - 1) * (↑x⁻¹ : A)) := by simp only [mul_assoc]
      _ = _ := by
        rw [LinearMap.trace_mul_cycle]
        simp only [mul_assoc]
  have hadd : b * ((↑⁅x, y⁆ : A) - 1) = b * d + b * ((↑⁅x, y⁆ : A) - 1 - d) := by
    noncomm_ring
  simp only [elementCharacter_apply, hadd, AddChar.map_add_eq_mul, htriv, mul_one,
    traceCharacter_apply, ht]

end Langlands.BushnellKutzko
