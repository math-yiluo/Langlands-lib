import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Dynamic.OppositeCellMono
import Langlands.GroupScheme.Dynamic.OppositeCellEmbedding

/-! # Proof of the opposite open cell for a smooth affine group over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The opposite open cell** (Conrad–Gabber–Prasad, Proposition 2.1.8(3)). For a smooth affine
group scheme `G` over a field, a cocharacter `χ` and representatives `iU` of `U(χ⁻¹)` and `iP` of
`P(χ)`, the multiplication `U ×_k P → G` is an open immersion. -/
theorem oppositeCellStatement : OppositeCellStatement.{u} := by
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
