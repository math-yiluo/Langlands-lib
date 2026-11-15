import Langlands.Representation.Aubert.General.CanonicalRationalTheorem17ReductionStatements
import Langlands.Representation.Aubert.General.CanonicalRationalTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalContragredientAssembly

/-! # Proof of the reduction of canonical contragredient commutation -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- The class form of induced Weyl conjugacy and the two finite-length-implies-
admissible targets at carrier universe `max (u + 1) v` imply Théorème 1.7 (1)
for the canonical actual operator. -/
theorem canonicalRationalContragredientCommutationReduction :
    CanonicalRationalContragredientCommutationReductionStatement.{u, v} := by
  intro hWeyl hadmG hadmM
  have hcomm : RationalContragredientCommutationStatement.{u, v} :=
    rationalContragredientCommutation_of_admissibility_and_inducedWeyl.{u, v}
      hadmG hadmM hWeyl
  exact canonicalRationalTargetBridges.{u, v}.1 hcomm

end Langlands.Aubert.General.RationalPointFamily
