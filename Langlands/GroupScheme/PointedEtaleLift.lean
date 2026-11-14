import Langlands.AlgebraicGeometry.SmoothPointedEtaleSectionConstruction
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Lifting a prescribed fibre point of a smooth group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S) (s : S)

/-- An actual section of the pulled-back group over a pointed étale neighbourhood,
with its prescribed residue-field value recorded by projection to the original group. -/
structure PointedEtaleGroupPointData
    (g₀ : Over.mk (𝟙 (Spec (S.residueField s))) ⟶
      ((baseChange (S.fromSpecResidueField s)).obj G).X) where
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ S
  residuePoint : Spec (S.residueField s) ⟶ neighbourhood
  etale : Etale projection
  residue_over : residuePoint ≫ projection = S.fromSpecResidueField s
  point : Over.mk (𝟙 neighbourhood) ⟶ ((baseChange projection).obj G).X
  recovers :
    residuePoint ≫ point.left ≫ pullback.fst G.X.hom projection =
      (baseChangeBasePointsEquiv (S.fromSpecResidueField s) G g₀).left

/-- Every prescribed residue-field point of a smooth group extends to a section
over a pointed étale neighbourhood of the base point. -/
def pointedEtaleGroupPoint [Smooth G.X.hom]
    (g₀ : Over.mk (𝟙 (Spec (S.residueField s))) ⟶
      ((baseChange (S.fromSpecResidueField s)).obj G).X) :
    PointedEtaleGroupPointData G s g₀ := by
  let a₀ : Over.mk (S.fromSpecResidueField s) ⟶ G.X :=
    baseChangeBasePointsEquiv (S.fromSpecResidueField s) G g₀
  let d := Langlands.AlgebraicGeometry.pointedEtaleSection
    G.X.hom s a₀.left (Over.w a₀)
  let a : Over.mk d.projection ⟶ G.X := Over.homMk d.sectionMap d.section_over
  let g := (baseChangeBasePointsEquiv d.projection G).symm a
  refine ⟨d.neighbourhood, d.projection, d.point, d.etale, d.point_over, g, ?_⟩
  have hg : g.left ≫ pullback.fst G.X.hom d.projection = d.sectionMap := by
    rw [← baseChangeBasePointsEquiv_left]
    exact congrArg Over.Hom.left
      ((baseChangeBasePointsEquiv d.projection G).apply_symm_apply a)
  rw [hg]
  exact d.recovers

namespace PointedEtaleGroupPointData

variable {G s}
  {g₀ : Over.mk (𝟙 (Spec (S.residueField s))) ⟶
    ((baseChange (S.fromSpecResidueField s)).obj G).X}
  (d : PointedEtaleGroupPointData G s g₀)

/-- The pointed étale neighbourhood contains a point above the specified base point. -/
theorem exists_point_over : ∃ x : d.neighbourhood, d.projection.base x = s := by
  refine ⟨d.residuePoint default, ?_⟩
  change (d.residuePoint ≫ d.projection) default = s
  rw [d.residue_over, Scheme.fromSpecResidueField_apply]

end PointedEtaleGroupPointData

end Langlands.GroupScheme
