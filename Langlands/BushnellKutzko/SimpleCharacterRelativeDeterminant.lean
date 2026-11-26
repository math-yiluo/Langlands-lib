import Langlands.BushnellKutzko.IntertwinedUnitCharacterStatement
import Langlands.BushnellKutzko.SimpleCharacterTransferComparison

/-! # The relative determinant criterion for simple-character domains -/

open ValuativeRel

namespace Langlands.BushnellKutzko

noncomputable section

universe uF uV

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Pullback to the relative chain turns centralizer intertwining into intertwining by every
relative endomorphism unit. -/
theorem factorsThroughCentralizerDet_of_relative_intertwining
    (hIntw : IntertwinedUnitCharacterStatement.{uV, uV}) (L : LatticeChain 𝒪[F] F V)
    {b : A} (hn : ∃ hE : IsField (elementAlgebra b), letI := hE.toField
      ∀ a : (elementAlgebra b)ˣ, subfieldUnits F (elementAlgebra b) V a ∈ L.stabilizer)
    {k : ℕ} (hk : 1 ≤ k) {H : Subgroup G}
    (hH : H ≤ L.unitFiltration k) (hU : relativeUnitFiltration L b k ≤ H)
    (θ : H →* ℂˣ) (hθ : (centralizerUnitGroup b : Set G) ⊆ characterSelfIntertwining θ) :
    factorsThroughCentralizerDet b θ := by
  obtain ⟨hE, hstab⟩ := hn
  let E := elementAlgebra b
  let := hE.toField
  let := L.finiteDimensional_subfield E
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let M := L.relativeLatticeChain hstab (isIntegral_iff_mem_spectralInteger F E)
  let ι := relativeEndUnits (F := F) (V := V) E
  let d := Units.map (LinearMap.det : Module.End E V →* E)
  have hB (v : (Module.End E V)ˣ) : ι v ∈ centralizerUnitGroup b := by
    rw [← relativeEndUnits_range_eq_centralizer b hE]
    exact ⟨v, rfl⟩
  have hu : (L.unitFiltration k).comap ι = M.unitFiltration k := by ext g; rfl
  have he : H.comap ι = M.unitFiltration k := by
    rw [← hu]
    exact le_antisymm (fun _ hg => hH hg) (fun g hg => hU ⟨hB g, hg⟩)
  let e := MulEquiv.subgroupCongr he.symm
  let φ := θ.comp ((ι.subgroupComap H).comp e.toMonoidHom)
  have hself (v : (Module.End E V)ˣ) : v ∈ characterSelfIntertwining φ := by
    intro x hx
    have hmem : ι v * ι x * (ι v)⁻¹ ∈ H := by
      have hh := (e ⟨v * (x : (Module.End E V)ˣ) * v⁻¹, hx⟩).prop
      change ι (v * (x : (Module.End E V)ˣ) * v⁻¹) ∈ H at hh
      simpa only [map_mul, map_inv] using hh
    have hv := hθ (hB v) (ι.subgroupComap H (e x)) hmem
    change θ ⟨ι v * ι x * (ι v)⁻¹, hmem⟩ = θ ⟨ι x, (e x).prop⟩ at hv
    change θ ⟨ι (v * (x : (Module.End E V)ˣ) * v⁻¹), _⟩ = θ ⟨ι x, _⟩
    simpa only [map_mul, map_inv] using hv
  obtain ⟨η, hη⟩ := hIntw E V M k hk φ hself
  let dH := d.comp (H.comap ι).subtype
  let dM := d.comp (M.unitFiltration k).subtype
  have hRange : dH.range ≤ dM.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨e.symm x, rfl⟩
  refine ⟨hE, η.comp (Subgroup.inclusion hRange), fun x => ?_⟩
  have he : Subgroup.inclusion hRange (dH.rangeRestrict x) = dM.rangeRestrict (e.symm x) :=
    Subtype.ext rfl
  change θ (ι.subgroupComap H x) = η (Subgroup.inclusion hRange (dH.rangeRestrict x))
  rw [he]
  have hv := hη (e.symm x)
  simpa only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hv

/-- A character of the simple-character domain intertwined by all the centralizer units
factors through the relative determinant on its centralizer intersection. -/
theorem factorsThroughCentralizerDet_of_intertwined_simpleHGroup
    (hIntw : IntertwinedUnitCharacterStatement.{uV, uV}) {S : Stratum 𝒪[F] F V} (hS : S.IsPure)
    (tail : List A) {m : ℕ} (θ : simpleHGroup S.chain S.n S.b tail (m + 1) →* ℂˣ)
    (hθ : (centralizerUnitGroup S.b : Set G) ⊆ characterSelfIntertwining θ) :
    factorsThroughCentralizerDet S.b θ :=
  factorsThroughCentralizerDet_of_relative_intertwining hIntw S.chain hS.1 (Nat.succ_pos m)
    (simpleHGroup_le_unitFiltration S.chain S.n S.b tail (m + 1))
    (relativeUnitFiltration_le_simpleHGroup S.chain S.n S.b tail (m + 1)) θ hθ

end

end Langlands.BushnellKutzko
