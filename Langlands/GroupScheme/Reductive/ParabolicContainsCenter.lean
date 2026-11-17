import Langlands.GroupScheme.SubgroupFunctor.FppfComap
import Langlands.GroupScheme.Reductive.RelativeCentralProductParabolic
import Langlands.GroupScheme.Reductive.RelativeCenterProof
import Langlands.GroupScheme.SubgroupFunctor.FpqcComap
import Mathlib.AlgebraicGeometry.Morphisms.Descent

/-! # Parabolic subgroups contain the centre; fppf inverse images reflect containment -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G P : GroupScheme S}

/-- Every relative parabolic subgroup of a reductive group scheme contains the
scheme-theoretic centre. -/
theorem IsRelativeParabolicSubgroup.center_le_range (hG : IsReductive G)
    {i : P ⟶ G} (hi : IsRelativeParabolicSubgroup i) :
    center G ≤ SubgroupFunctor.range i := by
  obtain ⟨Z, z, hz, -, -⟩ := reductiveRelativeCenter S G hG
  rw [← hz.2]
  exact hi.central_range_le hG i z hz.isCentral

end Langlands.GroupScheme
