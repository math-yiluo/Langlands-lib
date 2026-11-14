import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleSheaf
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSingletonCover

/-! # Actual parabolic descent along smooth surjective parameter maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)

/-- The parabolic presheaf satisfies the singleton sheaf condition along
an arbitrary smooth surjective parameter morphism. -/
theorem parabolic_isSheafFor_smooth {M T : Over S} (a : M ⟶ T)
    [Smooth a.left] [Surjective a.left] :
    Presieve.IsSheafFor (parabolicPresheaf G hG) (.singleton a) := by
  rw [Presieve.isSheafFor_iff_generate]
  exact parabolic_isSheaf_etale G hG _
    (Langlands.AlgebraicGeometry.AlgebraicSpace.generate_singleton_mem_etaleTopology_of_smooth a)

/-- Ordinary matching along any smooth surjective parameter map has a
unique actual parabolic descent. -/
theorem existsUnique_restrict_smooth {M T : Over S} (a : M ⟶ T)
    [Smooth a.left] [Surjective a.left]
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (hF : IsMatchingAlong hG a F) :
    ∃! H : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G),
      restrict hG a H = F :=
  Presieve.isSheafFor_singleton.mp (parabolic_isSheafFor_smooth hG a) F
    (fun {V} b c hab => hF V b c hab)

/-- Choose actual parabolic descent from ordinary smooth matching data. -/
def matchingSmooth {M T : Over S} (a : M ⟶ T)
    [Smooth a.left] [Surjective a.left]
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (hF : IsMatchingAlong hG a F) :
    ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G) :=
  (existsUnique_restrict_smooth hG a F hF).choose

/-- Smooth descent recovers exactly the prescribed actual local family. -/
@[simp]
theorem restrict_matchingSmooth {M T : Over S} (a : M ⟶ T)
    [Smooth a.left] [Surjective a.left]
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (hF : IsMatchingAlong hG a F) :
    restrict hG a (matchingSmooth hG a F hF) = F :=
  (existsUnique_restrict_smooth hG a F hF).choose_spec.1

/-- Actual parabolic families are detected by any smooth surjective
restriction, without a quasi-compactness hypothesis. -/
theorem restrict_injective_smooth {M T : Over S} (a : M ⟶ T)
    [Smooth a.left] [Surjective a.left] :
    Function.Injective (restrict hG a) := by
  intro F F' h
  obtain ⟨H, _, huniq⟩ := existsUnique_restrict_smooth hG a (restrict hG a F)
    (isMatchingAlong_restrict hG a F)
  exact (huniq F rfl).trans (huniq F' h.symm).symm

end Langlands.GroupScheme.ParabolicSubgroupModuli
