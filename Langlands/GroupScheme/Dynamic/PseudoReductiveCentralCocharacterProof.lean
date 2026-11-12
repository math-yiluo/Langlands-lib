import Langlands.GroupScheme.Dynamic.PseudoReductiveCentralCocharacterStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.TrivialUnipotentCentralizer
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof

/-!
# Proof of `Langlands.GroupScheme.PseudoReductiveCentralCocharacterStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Proof of `PseudoReductiveCentralCocharacterStatement`. -/
theorem pseudoReductiveCentralCocharacter : PseudoReductiveCentralCocharacterStatement.{u} := by
  intro k _ G hG χ
  let := hG.smooth
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_isUnipotent χ
    hG.hasTrivialUnipotentRadical
    (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χ)
    (dynamicUnipotentUnipotence k G χ _ _
      (Dynamic.Affine.isRepresentedBy_unipotentHom χ))

end Langlands.GroupScheme
