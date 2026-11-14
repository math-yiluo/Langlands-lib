import Langlands.GroupScheme.RelativeLevi.ParabolicMatching
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSheafGeneral

/-! # Zariski sheafness of actual parabolic subgroup families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S : Scheme.{u}} (G : GroupScheme S) (hG : IsReductive G)

/-- Compatible sections of the actual parabolic presheaf satisfy ordinary
parabolic-family matching. -/
theorem isMatchingParabolic_of_compatible {T : Over S}
    (𝒰 : Scheme.OpenCover.{u} T.left)
    (q : ∀ i, (parabolicPresheaf G hG).obj
      (op (SubgroupFunctor.coverObj 𝒰 i)))
    (hq : Presieve.Arrows.Compatible (parabolicPresheaf G hG)
      (fun i => SubgroupFunctor.coverMap 𝒰 i) q) :
    IsMatchingParabolic 𝒰 q hG := hq

/-- Actual parabolic sections admit unique gluing on every open cover of
an arbitrary parameter scheme. -/
theorem parabolic_isSheafFor_cover (T : Over S)
    (𝒰 : Scheme.OpenCover.{u} T.left) :
    Presieve.IsSheafFor (parabolicPresheaf G hG)
      (Langlands.AlgebraicGeometry.Picard.openCoverOver T 𝒰).presieve₀ := by
  apply (Presieve.isSheafFor_arrows_iff _ _).mpr
  intro q hq
  exact existsUnique_restrict 𝒰 q hG
    (isMatchingParabolic_of_compatible G hG 𝒰 q hq)

/-- The presheaf of actual relative parabolic subgroup functors of a
reductive group is a sheaf for the big Zariski topology on the slice. -/
theorem parabolic_isSheaf :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) (parabolicPresheaf G hG) :=
  Langlands.AlgebraicGeometry.Picard.isSheaf_zariski_over_of_openCover
    (parabolicPresheaf G hG) (parabolic_isSheafFor_cover G hG)

/-- The actual parabolic Zariski sheaf, retaining all-test subgroup functors
as its sections in `Type (u + 1)`. -/
def parabolicSheaf : Sheaf (Scheme.zariskiTopology.over S) (Type (u + 1)) :=
  ⟨parabolicPresheaf G hG,
    (isSheaf_iff_isSheaf_of_type _ _).mpr (parabolic_isSheaf G hG)⟩

end Langlands.GroupScheme.ParabolicSubgroupModuli
