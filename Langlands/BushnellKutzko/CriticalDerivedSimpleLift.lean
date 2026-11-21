import Langlands.BushnellKutzko.CriticalDerivedCyclicRows
import Langlands.BushnellKutzko.RefinementCore
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.SubfieldLayerLifting

/-! # Fieldness and the critical bound for the cyclic lift -/

noncomputable section

open ValuativeRel Polynomial IsLocalRing

namespace Langlands.BushnellKutzko.CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (C : LatticeChain 𝒪[F] F V)

set_option maxHeartbeats 600000 in
private theorem adjointLattice_le_of_shifting_commutants (c : Module.End F V) (d : ℤ)
    (hfield : IsField (elementAlgebra c))
    (hnorm : letI := hfield.toField
      ∀ a : (elementAlgebra c)ˣ, subfieldUnits F (elementAlgebra c) V a ∈ C.stabilizer)
    (hgen : ∀ x ∈ adjointLattice C c (d + 1), ∀ y ∈ elementAlgebra c, y ≠ 0 →
      ∃ (j : ℤ) (v : (Module.End F V)ˣ), (v : Module.End F V) = y ∧ Shifts C j v ∧
        (v : Module.End F V) ∈ leadingCommutant C x j) :
    adjointLattice C c (d + 1) ≤ centralizerLattice C c 0 ⊔ C.endFiltration 1 := by
  let : FiniteDimensional F V := C.finiteDimensional
  let E := elementAlgebra c
  let := hfield.toField
  let : FiniteDimensional F E := Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  let := subfieldIntegers_isDiscreteValuationRing F E
  let := subfieldIntegers_isFractionRing F E
  intro x hx
  let x₀ : C.order := ⟨x, C.mem_order_iff_mem_endFiltration.mpr hx.1⟩
  have hD (a : Eˣ) : a ∈ C.subfieldLayerCommutingSubgroup E hnorm (C.layerAction x₀) := by
    let y : Module.End F V := (a : E).val
    have hy₀ : y ≠ 0 := fun heq => a.ne_zero (Subtype.ext heq)
    obtain ⟨j, v, hv, hvShift, hvx⟩ := hgen x hx y (a : E).prop hy₀
    let g := C.subfieldStabilizer E hnorm a
    change C.LayerFamilyCommutes (C.layerAction x₀) g
    have hg : g = (⟨v, hvShift.mem_stabilizer⟩ : C.stabilizer) := by
      apply Subtype.ext
      apply Units.ext
      change (subfieldUnits F E V a : Module.End F V) = (v : Module.End F V)
      rw [coe_subfieldUnits, hv]
      rfl
    apply (C.layerAction_commutes_iff x₀ g).mpr
    rw [hg, hvShift.stabilizerValuation_eq]
    exact mem_leadingCommutant.mp hvx
  obtain ⟨y, hy, hDy⟩ := C.exists_subfield_lift_layers E hnorm (C.layerAction x₀) hD
  let yF := y.restrictScalars F
  have hyComm : Commute c yF := by
    change c * yF = yF * c
    ext v
    change (elementGenerator c : E) • y v = y ((elementGenerator c : E) • v)
    exact (y.map_smul (elementGenerator c) v).symm
  have hy₀ : yF ∈ centralizerLattice C c 0 :=
    ⟨C.mem_order_iff_mem_endFiltration.mp hy, sub_eq_zero.mpr hyComm.eq⟩
  have hdiff : x - yF ∈ C.endFiltration 1 :=
    (C.layerAction_eq_iff x₀ ⟨yF, hy⟩).mp fun i => (hDy i).symm
  exact Submodule.mem_sup.mpr ⟨yF, hy₀, x - yF, hdiff, by abel⟩

private theorem criticalExponent_le_of_adjointLattice_le (c : Module.End F V) (d : ℤ)
    (hfield : IsField (elementAlgebra c))
    (hnorm : letI := hfield.toField
      ∀ a : (elementAlgebra c)ˣ, subfieldUnits F (elementAlgebra c) V a ∈ C.stabilizer)
    (h : adjointLattice C c (d + 1) ≤ centralizerLattice C c 0 ⊔ C.endFiltration 1) :
    criticalExponent C c ≤ (d : WithBot ℤ) := by
  by_cases hbot : elementAlgebra c = ⊥
  · simp [criticalExponent, hbot]
  let : FiniteDimensional F V := C.finiteDimensional
  obtain ⟨j, hj, heq⟩ := exists_isGreatest_criticalIndexSet C c hfield hnorm hbot
  rw [heq, WithBot.coe_le_coe]
  by_contra! hlt
  exact hj.1 (h.trans' fun x hx => ⟨hx.1, C.endFiltration_antitone (by omega) hx.2⟩)

set_option maxHeartbeats 850000 in
/-- A shifting unit whose normalized residual operator satisfies a lifted irreducible
residual polynomial has a representative with the same leading symbol and with critical
exponent at most its shift. The generated field of the representative normalizes the chain. -/
theorem exists_simple_cyclic_lift {d : ℤ} (A : (Module.End F V)ˣ) (hA : Shifts C d A)
    {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (N : ShiftParameters C.period d)
    (P : (𝒪[F])[X]) (hP : P.Monic) (hP₀ : IsUnit (P.coeff 0))
    (hp : Irreducible (P.map (residue 𝒪[F])))
    (hzP : aeval (↑(N.residual A (scalarEndUnit (LatticeChain.uniformizerAsUnit hϖ))) : Module.End F V)
      (P.map (algebraMap 𝒪[F] F)) ∈ C.endFiltration 1) :
    ∃ c : Module.End F V, SymbolEq C d c A ∧
      (∃ hf : IsField (elementAlgebra c), letI := hf.toField
        ∀ a : (elementAlgebra c)ˣ, subfieldUnits F (elementAlgebra c) V a ∈ C.stabilizer) ∧
      criticalExponent C c ≤ (d : WithBot ℤ) := by
  let π₀ := LatticeChain.uniformizerAsUnit hϖ
  let π := scalarEndUnit (V := V) π₀
  let z := N.residual A π
  let τ := N.shift A π
  have hπ := uniformizerUnit_shifts hϖ C
  have hComm : Commute A π := (scalarEndUnit_commutes π₀ A).symm
  obtain ⟨hz, ht⟩ := N.shifts_residual_shift hA hπ
  let z₀ : C.order := ⟨z, C.mem_order_iff_mem_endFiltration.mpr hz.1⟩
  obtain ⟨B⟩ := exists_cyclicBasis C hϖ N.period_eq P hP hp z₀ hzP τ ht
  let Q := P.map (algebraMap 𝒪[F] F)
  have hQ : Q.Monic := hP.map _
  have hQf : Q.natDegree = P.natDegree := hP.natDegree_map _
  have hQc : IsUnit (Q.coeff 0) := by rw [show Q = _ from rfl, coeff_map]; exact hP₀.map _
  have hf : 0 < P.natDegree := by
    rw [← hP.natDegree_map (residue 𝒪[F])]
    exact natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hp)
  obtain ⟨M⟩ := exists_cyclicAlgebra Q hQ hQc π₀ N.u N.h_pos hQf hf
  have hU := actionU_symbol hϖ M B hQ hQf N.h_pos hf (N.residual_commutes_shift hComm) ht hz hzP
  have hT := actionT_symbol hϖ M B N.h_pos hf N.period_eq ht hz hπ (N.shift_carry hComm) hU
  have hUs := actionU_shifts M B hz hU
  have hTs := actionT_shifts M B ht hT
  let c := B.actionT M ^ N.k * B.actionU M ^ N.v
  have hsym : SymbolEq C d (c : Module.End F V) A := by
    have h := N.lifted_symbol hz ht hUs hTs hU hT
    rwa [N.reconstruct hComm] at h
  have hcs : Shifts C d c := by
    obtain ⟨v, hv, hs⟩ := exists_unit_of_symbolEq_self C hA hsym
    rwa [show v = c from Units.ext hv] at hs
  have hcRange : elementAlgebra (c : Module.End F V) ≤ (B.action M).range := by
    apply Algebra.adjoin_le
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    refine ⟨↑(M.T ^ N.k * M.U ^ N.v : M.Aˣ), ?_⟩
    change (↑(Units.map (B.action M).toMonoidHom (M.T ^ N.k * M.U ^ N.v)) : Module.End F V) = _
    rw [map_mul, map_zpow, map_zpow]
  obtain ⟨hfield, hnorm⟩ := isField_of_normalizingUnits C (y := (c : Module.End F V)) (fun y hy hy₀ => by
    obtain ⟨w, rfl⟩ := hcRange hy
    obtain ⟨j, v, hv, hvs, -⟩ := exists_shifts_of_cyclicAction hϖ C P M B hP hp N.period_eq N.g_pos
      hUs hTs (LeadingCommutant.of_commute 0 (Commute.zero_right _))
      (LeadingCommutant.of_commute N.g (Commute.zero_right _)) w hy₀
    exact ⟨v, hv, hvs.mem_stabilizer⟩)
  refine ⟨c, hsym, ⟨hfield, hnorm⟩, criticalExponent_le_of_adjointLattice_le C _ d hfield hnorm ?_⟩
  apply adjointLattice_le_of_shifting_commutants C _ d hfield hnorm
  intro x hx y hy hy₀
  have hcx : (c : Module.End F V) ∈ leadingCommutant C x d := mem_leadingCommutant.mpr hx.2
  obtain ⟨hc₁, hc₂⟩ := N.carry_reconstruct (B.action_commutes M)
    (scalarEndUnit_commutes π₀ (B.actionU M)) (B.actionT_carry M)
  change c ^ N.h = π ^ N.k * B.actionU M at hc₁
  change c ^ N.u * π ^ N.v = B.actionT M at hc₂
  have hc₃ : c ^ (N.h : ℤ) * π ^ (-N.k) = B.actionU M := by
    rw [zpow_natCast, ((scalarEndUnit_commutes π₀ (c ^ N.h)).zpow_left (-N.k)).symm.eq,
      hc₁, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
  have hπx (t : ℤ) : (↑(π ^ t) : Module.End F V) ∈ leadingCommutant C x (t * (C.period : ℤ)) := by
    apply LeadingCommutant.of_commute
    change ↑(Units.map (algebraMap F (Module.End F V)).toMonoidHom π₀ ^ t) * x =
      x * ↑(Units.map (algebraMap F (Module.End F V)).toMonoidHom π₀ ^ t)
    rw [← map_zpow (Units.map (algebraMap F (Module.End F V)).toMonoidHom), Units.coe_map]
    exact Algebra.commutes _ _
  have huz := LeadingCommutant.mul_mem (hcs.zpow (N.h : ℤ)).1 (hπ.zpow (-N.k)).1
    (LeadingCommutant.zpow_mem hcs hcx (N.h : ℤ)) (hπx (-N.k))
  have htz := LeadingCommutant.mul_mem (hcs.zpow N.u).1 (hπ.zpow N.v).1
    (LeadingCommutant.zpow_mem hcs hcx N.u) (hπx N.v)
  rw [← Units.val_mul, hc₃, N.residual_degree] at huz
  rw [← Units.val_mul, hc₂, N.shift_degree] at htz
  obtain ⟨w, rfl⟩ := hcRange hy
  exact exists_shifts_of_cyclicAction hϖ C P M B hP hp N.period_eq N.g_pos hUs hTs huz htz w hy₀

end Langlands.BushnellKutzko.CriticalDerived
