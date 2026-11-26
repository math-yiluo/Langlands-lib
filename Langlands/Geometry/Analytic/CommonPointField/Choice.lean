import Langlands.Geometry.Analytic.CommonPointField.Proof

/-! # A chosen common geometric point field -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A complete algebraically closed extension of `K` realizing all underlying points of `X`. -/
structure CommonPointField (X : LocalizedCategory.{u, v, v} (K := K)) where
  carrier : Type (max u (v + 1) uL)
  [normedField : NormedField carrier]
  [isUltrametricDist : IsUltrametricDist carrier]
  [completeSpace : CompleteSpace carrier]
  [isAlgClosed : IsAlgClosed carrier]
  [normedAlgebra : NormedAlgebra K carrier]
  projection_surjective : Function.Surjective ((localizedFieldPointProjection carrier).app X)

attribute [instance] CommonPointField.normedField CommonPointField.isUltrametricDist
  CommonPointField.completeSpace CommonPointField.isAlgClosed CommonPointField.normedAlgebra

/-- Select a common geometric point field of `X` by the proved common-field existence theorem. -/
def chooseCommonPointField (X : LocalizedCategory.{u, v, v} (K := K)) :
    CommonPointField.{u, v, uL} X :=
  Classical.choice (by
    obtain ⟨L, nL, uL', cL, aL, kL, hL⟩ := commonAlgebraicallyClosedPointField.{u, v, uL} K X
    exact ⟨{
      carrier := L
      normedField := nL
      isUltrametricDist := uL'
      completeSpace := cL
      isAlgClosed := aL
      normedAlgebra := kL
      projection_surjective := hL }⟩)

end Langlands.Analytic.SaturatedAtlasPresentation
