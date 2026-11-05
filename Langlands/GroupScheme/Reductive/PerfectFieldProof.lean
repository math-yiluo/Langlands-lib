import Langlands.GroupScheme.Reductive.PerfectFieldStatement
import Langlands.GroupScheme.Reductive.GaloisRadicalDescent
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Mathlib.FieldTheory.Galois.Basic

/-! # Perfect-field comparison of pseudo-reductivity and reductivity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every perfect field, pseudo-reductivity is connected reductivity. -/
theorem perfectFieldPseudoReductive :
    PerfectFieldPseudoReductiveStatement.{u} := by
  intro k _ _ G
  constructor
  · intro hG
    let : IsGalois k (AlgebraicClosure k) := ⟨⟩
    have hK := hG.baseChange_galois (K := AlgebraicClosure k)
    exact ⟨hG.smooth, hG.isAffineHom, hG.connectedSpace,
      hK.hasTrivialUnipotentRadical⟩
  · exact IsConnectedReductive.isPseudoReductive

end Langlands.GroupScheme
