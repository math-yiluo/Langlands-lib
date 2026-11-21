import Langlands.BaseChange.ExtensionInvariants
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
import Langlands.LocalField.PadicBridge
import Langlands.ClassFieldTheory.Local.NYLL.UniverseZeroModel

/-! # Transport of conductor and extension invariants on p-adic models -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis LocalClassField.NYLL ValuativeRel
open PadicField.TopologicalData

universe u v

section Characters

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p} {L : PadicField.{v} p}
  (T : K.TopologicalData) (S : L.TopologicalData) (e : K.Carrier ≃ₐ[Padic p] L.Carrier)

/-- Pullback on quasicharacters through a p-adic algebra equivalence for
the supplied topologies. -/
def padicCharacterPullback :
    letI := T.topology
    letI := S.topology
    Quasicharacter L.Carrier → Quasicharacter K.Carrier := by
  let := T.topology
  let := S.topology
  let := T.moduleTopology
  let := S.moduleTopology
  have := IsModuleTopology.toContinuousAdd (Padic p) L.Carrier
  exact fun χ => χ.comp
    { toMonoidHom := Units.map e.toMonoidHom
      continuous_toFun := (IsModuleTopology.continuous_of_linearMap
        e.toLinearEquiv.toLinearMap).units_map _ }

/-- The first trivial principal-unit level is invariant under pullback. -/
theorem padicCharacterPullback_multiplicativeConductor :
    letI := S.topology
    ∀ χ : Quasicharacter L.Carrier,
      T.toLocalFieldData.multiplicativeConductor (padicCharacterPullback T S e χ) =
        S.toLocalFieldData.multiplicativeConductor χ := by
  let := S.topology
  intro χ
  let eU := Units.mapEquiv e.toMulEquiv
  have hu (n : ℕ) (a : K.Carrierˣ) :
      eU a ∈ S.toLocalFieldData.principalUnits n ↔ a ∈ T.toLocalFieldData.principalUnits n := by
    change eU a ∈ S.principalUnits n ↔ a ∈ T.principalUnits n
    simp only [mem_principalUnits]
    change (S.discreteValuation (e (a : K.Carrier)) = 1 ∧
      S.discreteValuation (e (a : K.Carrier) - 1) ≤ _) ↔ _
    rw [← map_one e, ← map_sub e, discreteValuation_eq_of_algEquiv e T S,
      discreteValuation_eq_of_algEquiv e T S]
  let χ' := padicCharacterPullback T S e χ
  apply le_antisymm
  · apply (T.toLocalFieldData.multiplicativeTrivialAt_iff_conductor_le _ _).mp
    intro a ha
    exact S.toLocalFieldData.multiplicativeConductor_spec χ _ ((hu _ a).mpr ha)
  · apply (S.toLocalFieldData.multiplicativeTrivialAt_iff_conductor_le _ _).mp
    intro b hb
    obtain ⟨a, rfl⟩ := eU.surjective b
    exact T.toLocalFieldData.multiplicativeConductor_spec χ' _ ((hu _ a).mp hb)

end Characters

section Extension

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] (T : F.TopologicalData) (S : E.TopologicalData)

local notation "F₀" => universeZeroModel F
local notation "E₀" => universeZeroModel E

omit [Algebra F.Carrier E.Carrier] in
/-- The residue-cardinality definition of the degree is preserved in the model. -/
theorem isResidueDegree_universeZero {f : ℕ}
    (h : letI := T.valuativeRel; letI := S.valuativeRel; IsResidueDegree F.Carrier E.Carrier f) :
    letI := (F₀).canonicalTopologicalData.valuativeRel
    letI := (E₀).canonicalTopologicalData.valuativeRel
    IsResidueDegree (F₀).Carrier (E₀).Carrier f := by
  change (E₀).canonicalTopologicalData.residueCardinality =
    (F₀).canonicalTopologicalData.residueCardinality ^ f
  change S.residueCardinality = T.residueCardinality ^ f at h
  calc
    _ = S.residueCardinality :=
      (residueCardinality_eq_of_algEquiv (universeZeroEquiv E) (E₀).canonicalTopologicalData S).symm
    _ = T.residueCardinality ^ f := h
    _ = _ := congrArg (fun n : ℕ => n ^ f)
      (residueCardinality_eq_of_algEquiv (universeZeroEquiv F) (F₀).canonicalTopologicalData T)

/-- The trace-codifferent definition of the exponent is preserved in the model. -/
theorem isDifferentExponent_universeZero {d : ℕ}
    (h : letI := T.valuativeRel; letI := S.valuativeRel; IsDifferentExponent F.Carrier E.Carrier d) :
    letI := universeZeroAlgebra F E
    letI := (F₀).canonicalTopologicalData.valuativeRel
    letI := (E₀).canonicalTopologicalData.valuativeRel
    IsDifferentExponent (F₀).Carrier (E₀).Carrier d := by
  let T₀ := (F₀).canonicalTopologicalData
  let S₀ := (E₀).canonicalTopologicalData
  let := T₀.valuativeRel
  let := S₀.topology
  let := S₀.valuativeRel
  let := S₀.localField
  let := T.valuativeRel
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let := universeZeroAlgebra F E
  let eF := universeZeroEquiv F
  let eE := universeZeroEquiv E
  have hiF (x : (F₀).Carrier) : eF x ∈ T.Integers ↔ x ∈ T₀.Integers := by
    rw [T.mem_integers_iff_discreteValuation_le_one, T₀.mem_integers_iff_discreteValuation_le_one,
      discreteValuation_eq_of_algEquiv eF T₀ T]
  have hiE (x : (E₀).Carrier) : eE x ∈ S.Integers ↔ x ∈ S₀.Integers := by
    rw [S.mem_integers_iff_discreteValuation_le_one, S₀.mem_integers_iff_discreteValuation_le_one,
      discreteValuation_eq_of_algEquiv eE S₀ S]
  have htrace (x : (E₀).Carrier) : eF (Algebra.trace (F₀).Carrier (E₀).Carrier x) =
      Algebra.trace F.Carrier E.Carrier (eE x) := by
    rw [Algebra.trace_eq_of_equiv_equiv eF.toRingEquiv eE.toRingEquiv
      (universeZeroAlgebra_compatible F E)]
    exact eF.toRingEquiv.apply_symm_apply _
  obtain ⟨ϖ, hϖ, hcod⟩ := h
  let ϖ₀ := Units.map (eE.symm.toMonoidHom) ϖ
  have hϖ₀ : eE (ϖ₀ : (E₀).Carrier) = (ϖ : E.Carrier) := eE.apply_symm_apply _
  refine ⟨ϖ₀, ⟨?_, ?_⟩, fun x => ?_⟩
  · let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (E₀).Carrier
    apply e.strictMono.lt_iff_lt.mp
    change S₀.discreteValuation (ϖ₀ : (E₀).Carrier) < e 1
    rw [map_one, ← discreteValuation_eq_of_algEquiv eE S₀ S, hϖ₀]
    let e' := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E.Carrier
    change e' (valuation E.Carrier (ϖ : E.Carrier)) < 1
    rw [← map_one e']
    exact e'.strictMono hϖ.1
  · intro x hx
    obtain ⟨m, hm⟩ := hϖ.2 (eE x) ((map_ne_zero eE).mpr hx)
    refine ⟨m, ?_⟩
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (E₀).Carrier
    let e' := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E.Carrier
    apply e.injective
    rw [map_zpow₀]
    change S₀.discreteValuation x = S₀.discreteValuation (ϖ₀ : (E₀).Carrier) ^ m
    rw [← discreteValuation_eq_of_algEquiv eE S₀ S x,
      ← discreteValuation_eq_of_algEquiv eE S₀ S (ϖ₀ : (E₀).Carrier), hϖ₀]
    exact (congrArg e' hm).trans (map_zpow₀ e' _ _)
  · have htr (y : (E₀).Carrier) :
        Algebra.trace (F₀).Carrier (E₀).Carrier (x * y) ∈ T₀.Integers ↔
          Algebra.trace F.Carrier E.Carrier (eE x * eE y) ∈ T.Integers := by
      rw [← hiF, htrace, map_mul]
    refine Iff.trans ?_ ((hcod (eE x)).trans ?_)
    · constructor
      · intro hx y hy
        obtain ⟨z, rfl⟩ := eE.surjective y
        exact (htr z).mp (hx z ((hiE z).mp hy))
      · intro hx y hy
        exact (htr y).mpr (hx _ ((hiE y).mpr hy))
    · rw [← hiE, map_mul, map_pow, hϖ₀]

end Extension

end Langlands.BaseChange
