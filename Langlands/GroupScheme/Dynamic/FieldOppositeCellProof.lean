import Langlands.GroupScheme.Dynamic.FieldOppositeCellStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Dynamic.OppositeCellMono
import Langlands.GroupScheme.Dynamic.OppositeCellEmbedding

/-! # Proof of the opposite dynamic open cell over a field without smoothness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The opposite dynamic open cell for an affine finite-type group over a field. -/
theorem dynamicFieldOppositeCell : DynamicFieldOppositeCellStatement.{u} := by
  intro k _ G _ _ χ U P iU iP hU hP
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  obtain ⟨g, e, he⟩ := GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter k (χ ≫ ρ)
  let ι := ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g)
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : IsIso ι.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso ι)).hom)
  have : IsClosedImmersion (ρ ≫ ι.hom).hom.hom.left :=
    (inferInstance : IsClosedImmersion (ρ.hom.hom.left ≫ ι.hom.hom.hom.left))
  exact Dynamic.isOpenImmersion_mul_of_diagonal (ρ := ρ ≫ ι.hom)
    (by rw [← Category.assoc]; exact he) hU hP (Dynamic.mono_oppositeCellMul χ hU hP)

end Langlands.GroupScheme
