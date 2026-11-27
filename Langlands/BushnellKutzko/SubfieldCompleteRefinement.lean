import Langlands.BushnellKutzko.CompleteLatticeRefinement
import Langlands.BushnellKutzko.LatticeRefinementBounds
import Langlands.BushnellKutzko.PureStratumApproximationMoyTransport
import Langlands.BushnellKutzko.RelativeLatticeChain
import Langlands.BushnellKutzko.SubfieldCompleteRefinementStatement

/-! # Complete refinement of the chain over the parameter field -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

set_option maxHeartbeats 1000000 in
/-- The complete relative chain lifts to the base field with the same
lattice subsets and the corresponding unit-group bounds. -/
theorem subfieldCompleteRefinement : SubfieldCompleteRefinementStatement.{uF, uE, uV} := by
  intro F _ _ _ _ E _ _ V _ _ _ _ L hE
  let _ := L.finiteDimensional_subfield E
  let _ := LocalField.FiniteExtension.normedField F E
  let _ := LocalField.FiniteExtension.valuativeRel F E
  let _ := LocalField.FiniteExtension.isLocalField F E
  let _ := subfieldIntegers_isDiscreteValuationRing F E
  let φ := subfieldIntegerEquiv F E
  let A := L.relativeLatticeChain hE (isIntegral_iff_mem_spectralInteger F E)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  have hπ : Irreducible (φ ϖ) := (MulEquiv.irreducible_iff φ.toMulEquiv).mpr hϖ
  obtain ⟨B, hBp, hB₀, hB⟩ := A.exists_complete_refinement hπ
  let C := B.transfer φ.symm (fun _ => rfl)
  have hCp : C.period = Module.finrank E V :=
    (PureApproximation.period_eq_of_coe_lattice_eq C B (fun _ => rfl) hϖ hπ rfl).trans hBp
  let M := PureApproximation.liftChain C
  have hM (i : ℤ) : ∃ j : ℤ, M.lattice j = L.lattice i := by
    obtain ⟨j, hj⟩ := hB i
    have h : (B.lattice j : Set V) = A.lattice i := congrArg SetLike.coe hj
    exact ⟨j, SetLike.coe_injective h⟩
  have hM₀ : M.lattice 0 = L.lattice 0 := by
    have h : (B.lattice 0 : Set V) = A.lattice 0 := congrArg SetLike.coe hB₀
    exact SetLike.coe_injective h
  have hp : M.period = subfieldRamificationIndex F E * Module.finrank E V := by
    rw [PureApproximation.liftChain_period, hCp]
  obtain ⟨hU, hU₁⟩ := LatticeChain.refinement_unitFiltration_bounds hM
  exact ⟨M, PureApproximation.liftChain_normalized C, hM₀, hM, hp, hU, hU₁,
    C, hCp, fun _ => rfl⟩

end Langlands.BushnellKutzko
