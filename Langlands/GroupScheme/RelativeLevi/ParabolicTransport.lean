import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange

/-! # Relative parabolic transport compatibility import

The canonical presentation-transport and base-change declarations are provided by
`RelativeLevi.ParabolicBaseChange`.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace Langlands.GroupScheme
variable {S S' : Scheme.{u}} {G P : GroupScheme S}

/-- The actual base-changed inclusion, retaining its relative parabolicity. -/
def relativeParabolicBaseChangeOfInclusion (b : S' ⟶ S) (hG : IsReductive G)
    (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i) :
    {j : (baseChange b).obj P ⟶ (baseChange b).obj G //
      IsRelativeParabolicSubgroup j} :=
  ⟨(baseChange b).map i, hi.baseChange hG b⟩

@[simp]
theorem relativeParabolicBaseChangeOfInclusion_val (b : S' ⟶ S) (hG : IsReductive G)
    (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i) :
    (relativeParabolicBaseChangeOfInclusion b hG i hi).val = (baseChange b).map i := rfl


end Langlands.GroupScheme
