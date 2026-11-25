import Langlands.Geometry.Building.IwahoriDecompositionAxiomStatement
import Langlands.Geometry.Building.IwahoriDecompositionAxiomReduction
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylProof

/-! # Axiom 4.1.16 for the building of a valuation of the root datum: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **KP Axiom 4.1.16 (Iwahori decomposition)** for the building of supplied data over a
nonarchimedean local field, under V 7 and AS 2–AS 5: for every chamber `C` and every generic
cocharacter, the Iwahori subgroup `I` is the bijective product
`(U^+(F) ∩ I) × Z(F)^0 × (U^-(F) ∩ I)`, and `U^±(F) ∩ I` are the bijective ordered products of
the groups `U_{ψ_a}`. -/
theorem iwahoriDecompositionAxiom : IwahoriDecompositionAxiomStatement.{u} :=
  iwahoriDecompositionAxiomReduction simplyConnectedNormalizerAffineWeyl

end Langlands.Geometry.Building
