import Langlands.GroupScheme.SubgroupFunctor.FppfProductImage

/-! # Uniqueness of actual fppf subgroup images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor.IsFppfImage

variable {B : Scheme.{u}} {G Q : GroupScheme B}
    {F : SubgroupFunctor G} {E E' : SubgroupFunctor Q} {q : G ⟶ Q}

/-- Every represented subgroup containing the ordinary image contains the
actual fppf image, by the published fppf-local minimality theorem. -/
theorem le_of_map_le_of_isRepresentedBy (h : IsFppfImage F E q)
    {K' : GroupScheme B} {j' : K' ⟶ Q} (hj' : E'.IsRepresentedBy j')
    (hle : F.map q ≤ E') : E ≤ E' := by
  let : Mono j'.hom.hom := hj'.1
  apply h.le_of_map_le _ hle
  rw [← hj'.2]
  exact isFppfLocal_range j'

/-- The represented actual fppf image of a fixed subgroup and map is unique. -/
theorem unique (h : IsFppfImage F E q) (h' : IsFppfImage F E' q) : E = E' := by
  obtain ⟨H, K, i, j, p, hi, hj, hp⟩ := h
  obtain ⟨H', K', i', j', p', hi', hj', hp'⟩ := h'
  exact le_antisymm
    ((show IsFppfImage F E q from ⟨H, K, i, j, p, hi, hj, hp⟩).le_of_map_le_of_isRepresentedBy
      hj' (show IsFppfImage F E' q from ⟨H', K', i', j', p', hi', hj', hp'⟩).map_le)
    ((show IsFppfImage F E' q from ⟨H', K', i', j', p', hi', hj', hp'⟩).le_of_map_le_of_isRepresentedBy
      hj (show IsFppfImage F E q from ⟨H, K, i, j, p, hi, hj, hp⟩).map_le)

end Langlands.GroupScheme.SubgroupFunctor.IsFppfImage
