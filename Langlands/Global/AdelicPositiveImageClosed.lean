import Langlands.Global.AdelicLogSection
import Langlands.GroupScheme.AffinePointClosedImmersion

/-! # Closed positive adelic images under actual closed immersions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj RestrictedProduct

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
variable (G H : GroupScheme (Spec (CommRingCat.of F)))
variable [IsAffine G.X.left] [IsAffine H.X.left]

/-- A genuine closed immersion is a closed embedding on actual adelic points. -/
theorem isClosedEmbedding_map (f : G ⟶ H) [IsClosedImmersion f.hom.hom.left] :
    IsClosedEmbedding (map F G H f) := by
  let : T2Space (InfiniteAdeles F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  let : T2Space (FiniteAdeles F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : T2Space (Adeles F) :=
    inferInstanceAs (T2Space (InfiniteAdeles F × FiniteAdeles F))
  exact GroupScheme.isClosedEmbedding_affinePointsTarget G H
    (CommAlgCat.of F (Adeles F)) f

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (i : T.toGrp ⟶ G)

/-- The existing actual positive adelic image is the range of its point map. -/
theorem range_positivePointMap :
    Set.range (positivePointMap F G T i) =
      (imageSubgroup F T G i : Set (AdelicGroupPoints F G)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

variable [IsAffine G.X.left] [IsAffine T.X.left]
variable [IsClosedImmersion i.hom.hom.left]

/-- Restricting the actual closed-immersion map to intrinsic positive points
is a closed embedding without a character-detection assumption. -/
theorem isClosedEmbedding_positivePointMap :
    IsClosedEmbedding (positivePointMap F G T i) :=
  (AdelicGroupPoints.isClosedEmbedding_map F T.toGrp G i).comp
    (isClosed_intrinsicSubgroup F T).isClosedEmbedding_subtypeVal

/-- The existing intrinsic positive image is closed in the ambient adelic group. -/
theorem isClosed_imageSubgroup :
    IsClosed (imageSubgroup F T G i : Set (AdelicGroupPoints F G)) := by
  rw [← range_positivePointMap F G T i]
  exact (isClosedEmbedding_positivePointMap F G T i).isClosed_range

/-- The existing image subgroup, bundled with its proved ambient closedness. -/
def closedImageSubgroup : ClosedSubgroup (AdelicGroupPoints F G) where
  toSubgroup := imageSubgroup F T G i
  isClosed' := isClosed_imageSubgroup F G T i

@[simp] theorem closedImageSubgroup_toSubgroup :
    (closedImageSubgroup F G T i).toSubgroup = imageSubgroup F T G i := rfl

end Langlands.Global.PositiveRealTorus
