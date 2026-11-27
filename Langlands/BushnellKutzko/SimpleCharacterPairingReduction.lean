import Langlands.BushnellKutzko.SimpleCharacterRelativeCommutators
import Langlands.BushnellKutzko.CommutatorPairing
import Langlands.BushnellKutzko.SimpleCharacterPairingStatement

/-! # Descent of the simple-character commutator form -/

open ValuativeRel
open scoped commutatorElement

namespace Langlands.BushnellKutzko

universe uF uV

/-- Reduction of (3.4.1) to the subgroup properties and relative commutator laws. -/
theorem simpleCharacterPairing_of_relativeCommutatorLaws
    (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    (hG : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (hR : SimpleCharacterRelativeCommutatorLaws.{uF,uV}) :
    SimpleCharacterPairingStatement.{uF,uV} := by
  intro F _ _ _ _ V _ _ ψ hψ S hS0 hS q i
  dsimp only
  intro hn hd θ hθ
  let m := i + 1
  let H := simpleHGroup S.chain S.n S.b q.tail m
  let J := simpleJGroup S.chain S.n S.b q.tail m
  let G := (Module.End F V)ˣ
  let A := Module.End F V
  let QJ := simpleJLayer S.chain S.n S.b q.tail m
  have hm : 1 ≤ m := by omega
  have hpairwise : m ≤ m + m := by omega
  have hi : (i : ℤ) < finiteCriticalDepth S.chain S.n S.b := by
    by_cases he : q.steps = 0
    · rw [SimpleStratum.terminal_depth S q he]
      omega
    · obtain ⟨T, q', r, -, -, -, -, -, -, hcrit, -, -, -, -⟩ :=
        q.exists_suffix hS0 (Nat.pos_of_ne_zero he)
      rw [simpleCriticalDepth_eq_of_criticalExponent hcrit] at hd
      have hd' := WithTop.coe_le_coe.mp hd
      rw [finiteCriticalDepth_eq_of_criticalExponent S.chain S.n S.b r hcrit]
      omega
  have hHJ : H ≤ J := ((hG F V S hS0 hS q).2.2.2.1 m).1
  have hcomm (x y : J) : ⁅(x : G), (y : G)⁆ ∈ H :=
    SimpleStratum.commutator_mem_HGroup hG S hS0 hS q hm hm hpairwise x.property y.property
  have hxJ (x : J) : ((x : G) : A)-1 ∈ QJ :=
    (simpleJGroup_mem_iff_of_pos S hS0 hS q hm).mp x.property
  have hval (x y : J) :
      (θ ⟨_, hcomm x y⟩ : ℂ) = adjointCharacterPair ψ S.b (((x : G) : A)-1) (((y : G) : A)-1) :=
    SimpleStratum.simpleCharacter_commutator_eq_adjointPair hL hG hR ψ hψ S hS0 hS q
      hi hm hpairwise hθ x.property y.property (hcomm x y)
  have hrad (x : J) : (∀ y : J, θ ⟨_, hcomm x y⟩ = 1) ↔ (x : G) ∈ H := by
    rw [simpleHGroup_mem_iff_of_pos S hS0 hS q hm,
      SimpleStratum.mem_simpleHLayer_iff_adjointCharacterPair S q hS0 hS ψ hψ (hxJ x)]
    constructor
    · intro hy y hyJ
      obtain ⟨g, _, hgy⟩ := S.chain.exists_mem_unitFiltration hm hyJ.2
      have hy' : (g : A) - 1 = y := by rw [hgy]; abel
      have hgJ : g ∈ J := (simpleJGroup_mem_iff_of_pos S hS0 hS q hm).mpr (hy'.symm ▸ hyJ)
      have he := hy ⟨g, hgJ⟩
      have hv := hval x ⟨g, hgJ⟩
      change (θ ⟨_, hcomm x ⟨g, hgJ⟩⟩ : ℂ) =
        adjointCharacterPair ψ S.b (((x : G) : A)-1) ((g : A)-1) at hv
      rw [he, Units.val_one, hy'] at hv
      exact hv.symm
    · intro hy y
      apply Units.ext
      exact (hval x y).trans (hy _ (hxJ y))
  obtain ⟨hN, B, hvalue, hAlt, hNondeg⟩ := exists_quotientCommutatorPairing hHJ θ hcomm hrad
  exact ⟨hHJ, hN, B, fun x y => ⟨hcomm x y, hvalue x y⟩, hAlt, hNondeg⟩

/-- The simple-character pairing follows from the subgroup and lattice
properties and the finite-depth mixed commutator calculation. -/
theorem simpleCharacterPairing_of_mixedJ
    (hL : SimpleStratumLatticePropertiesStatement.{uF,uV})
    (hG : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (hM : SimpleCharacterMixedJCommutator.{uF,uV}) :
    SimpleCharacterPairingStatement.{uF,uV} :=
  simpleCharacterPairing_of_relativeCommutatorLaws hL hG
    (SimpleStratum.relativeCommutatorLaws_of_mixedJ hG hM)

end Langlands.BushnellKutzko
