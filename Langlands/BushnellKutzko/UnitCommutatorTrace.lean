import Langlands.BushnellKutzko.TerminalSimpleCharacter
import Langlands.BushnellKutzko.SimpleStratumPairingDual
import Langlands.BushnellKutzko.CharacterCommutatorDepth
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh

/-! # Trace-character evaluation of filtered unit commutators -/

open ValuativeRel
open scoped commutatorElement

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => Aˣ

variable [ValuativeRel F]

local notation "O" => 𝒪[F]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A trace-character twist at depth `−r` evaluates a filtered commutator through
its leading ring commutator when the error lies in the conductor. -/
theorem elementCharacter_commutator_eq_adjointCharacterPair (L : LatticeChain O F V)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) {b : A} {r : ℤ}
    {x y : G} {k l : ℕ} (hb : b ∈ L.endFiltration (-r))
    (hx : x ∈ L.unitFiltration k) (hy : y ∈ L.unitFiltration l)
    (hdepth : r < (k : ℤ) + (l : ℤ) + ((min k l : ℕ) : ℤ)) :
    elementCharacter (traceCharacter ψ) b ⁅x, y⁆ = adjointCharacterPair ψ b ((x : A) - 1) ((y : A) - 1) := by
  let D := ((x : A) - 1) * ((y : A) - 1) - ((y : A) - 1) * ((x : A) - 1)
  let E := ((↑x⁻¹ : A) - 1) * (↑y⁻¹ : A) + ((↑y⁻¹ : A) - 1)
  have hD : D ∈ L.endFiltration ((k : ℤ) + (l : ℤ)) :=
    sub_mem (L.mul_mem_endFiltration hx.2.2 hy.2.2)
      (by simpa only [add_comm] using L.mul_mem_endFiltration hy.2.2 hx.2.2)
  have hE : E ∈ L.endFiltration (min k l : ℕ) := by
    have hxi := (L.unitFiltration k).inv_mem hx
    have hyi := (L.unitFiltration l).inv_mem hy
    have hxi₀ := L.mul_mem_endFiltration hxi.2.2 (L.mem_order_iff_mem_endFiltration.mp hy.2.1)
    refine add_mem (L.endFiltration_antitone ?_ (by simpa only [add_zero] using hxi₀))
      (L.endFiltration_antitone ?_ hyi.2.2)
    · exact_mod_cast min_le_left k l
    · exact_mod_cast min_le_right k l
  have hE' := L.endFiltration_antitone (by omega : 1 ≤ -r + (k + l) + (min k l : ℕ))
    (L.mul_mem_endFiltration (L.mul_mem_endFiltration hb hD) hE)
  have hnull := traceCharacter_eq_one_of_mem L ψ hψ hE'
  have heq : b * ((↑(⁅x, y⁆) : A) - 1) = b * D + b * D * E := by
    rw [commutatorElement_sub_one]
    change b * (D * (↑x⁻¹ : A) * (↑y⁻¹ : A)) = _
    dsimp only [E]
    noncomm_ring
  rw [elementCharacter_apply, heq, AddChar.map_add_eq_mul, hnull, mul_one]
  exact traceCharacter_mul_ringCommutator ψ b _ _

/-- The filtered conjugation formula is trivial when the first unit centralizes
the parameter. -/
theorem elementCharacter_commutator_eq_one_of_commute (L : LatticeChain O F V)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) {b : A} {r : ℤ}
    {x y : G} {k l : ℕ} (hb : b ∈ L.endFiltration (-r))
    (hx : x ∈ L.unitFiltration k) (hy : y ∈ L.unitFiltration l)
    (hbx : Commute b (x : A)) (hdepth : r < (k : ℤ) + 2 * (l : ℤ)) :
    elementCharacter (traceCharacter ψ) b ⁅x, y⁆ = 1 := by
  have hconj : (↑x⁻¹ : A) * b * (x : A) - b = 0 := by
    rw [mul_assoc, hbx.eq, ← mul_assoc, Units.inv_mul, one_mul, sub_self]
  rw [elementCharacter_commutator_of_depth L ψ hψ hb (by omega) hx hy,
    hconj, elementCharacter_apply, zero_mul, AddChar.map_zero_eq_one]

end Langlands.BushnellKutzko
