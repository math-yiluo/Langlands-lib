import Langlands.Geometry.Building.DoubleCosetStatementReduction
import Langlands.Geometry.Building.IwahoriWeylProof
import Langlands.Geometry.Building.AffineIwahoriTitsProof

/-! # Proof of the Iwahori double-coset bijection (corrected KP Theorem 7.8.1(2))

The published reduction `iwahoriDoubleCosetStatement_of_statements` derives
`IwahoriDoubleCosetStatement` from the chamber splitting of KP 7.8.2 and the actual affine
Iwahori–Tits system of KP Theorem 7.5.3. Both are proved in the Library:
`iwahoriWeylChamberSplitting` and `affineIwahoriTits`. The injectivity argument implemented
by the reduction's adapters is the one of the authors' 2024 corrections: decompose along the
chamber splitting, compare components, and apply Bruhat uniqueness in `G(F)^0`.
-/

universe u

namespace Langlands.Geometry.Building

/-- **KP Theorem 7.8.1(2), with the corrected injectivity proof.** For parahoric building
data satisfying the apartment axioms and every chamber `C` of the apartment, with Iwahori
subgroup `I = P_C`, the map `W̃^0 → I\G(F)/I`, `n ↦ I n I`, is a bijection. -/
theorem iwahoriDoubleCoset : IwahoriDoubleCosetStatement.{u} :=
  iwahoriDoubleCosetStatement_of_statements iwahoriWeylChamberSplitting affineIwahoriTits

end Langlands.Geometry.Building
