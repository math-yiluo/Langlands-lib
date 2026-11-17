import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleSchemeStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleAtlasCharts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Schemes from separated algebraic spaces with structurally etale atlases -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A separated algebraic space admitting an etale structural scheme atlas
is represented by an actual scheme over the original base. -/
theorem separatedEtaleScheme : SeparatedEtaleSchemeStatement.{u} := by
  intro S X hsep hX
  obtain ⟨U, a, ha, hs, hU⟩ := hX
  let Y : Over S := Over.mk (𝟙 S)
  let hY : IsTerminal ((schemeYoneda S).obj Y) :=
    Over.mkIdTerminal.isTerminalObj (schemeYoneda S)
  let f := hY.from X.presheaf
  let w : U ⟶ Y := Over.homMk U.hom (by simp [Y])
  let : Etale w.left := hU
  exact SeparatedEtaleImages.exists_representation_of_etale_composite
    X.toSheaf hsep a ha hs f w (hY.hom_ext _ _)

end Langlands.AlgebraicGeometry.AlgebraicSpace
