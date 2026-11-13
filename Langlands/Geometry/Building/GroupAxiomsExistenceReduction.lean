import Langlands.Geometry.Building.GroupAxiomsExistenceReductionStatement

/-! # Proof of `GroupAxiomsExistenceReductionStatement` -/

universe u

namespace Langlands.Geometry.Building

/-- Proof of `GroupAxiomsExistenceReductionStatement`: the construction premise gives `P`, `R`,
`T` with the seven predicates, the integral-model premise applied to them gives `M`, `Q`, `ρ`
with Axioms 4.1.20 and 4.1.22, and the root-group and Iwahori premises applied to `P` and its
`SatisfiesApartmentAxioms` give Axiom 4.1.8 (2)–(3) and Axiom 4.1.16. The datum
`⟨P, R, T, M, Q, ρ⟩` satisfies `SatisfiesGroupAxioms` field by field; Axiom 4.1.8 (1) comes from
`KPBuildingDatum.satisfiesRootGroupActionAxiom_iff`. -/
theorem groupAxiomsExistenceReduction : GroupAxiomsExistenceReductionStatement.{u} := by
  intro hC hR hI hM F _ _ _ _ G _ hG
  obtain ⟨P, R, T, hB, hO, hA, hRR, hD, hF, hT⟩ := hC F G hG
  obtain ⟨M, Q, ρ, hMA, hQA⟩ := hM F G P R T hB hO hA hRR hD hF hT
  obtain ⟨hZ, hU⟩ := hR F G P hD
  exact ⟨⟨P, R, T, M, Q, ρ⟩,
    { building := hB
      boundedSubgroups := hO
      affineStructure := hA
      affineRootSystem := ⟨hRR, hD, hF⟩
      rootGroupAction := (KPBuildingDatum.satisfiesRootGroupActionAxiom_iff _).2 ⟨hZ, hU⟩
      titsSystem := hT
      iwahoriDecomposition := hI F G P hD
      bruhatTitsGroupSchemes := hMA
      reductiveQuotients := hQA }⟩

end Langlands.Geometry.Building
