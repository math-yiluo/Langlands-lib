import Langlands.GroupScheme.RelativeLevi.ParabolicAffineEtaleDescent
import Langlands.GroupScheme.RelativeLevi.ParabolicMatching
import Langlands.GroupScheme.HomScheme.TorusChartDescent

/-! # Ordinary matching over an affine surjective étale parameter map -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open TorusSubgroupModuli Descent

variable {S : Scheme.{u}} {G : GroupScheme S} {M T : Over S}

/-- Ordinary matching along a parameter morphism: any two comparisons with
the same composite give the same restricted actual parabolic. -/
def IsMatchingAlong (hG : IsReductive G) (a : M ⟶ T)
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G)) : Prop :=
  ∀ (V : Over S) (b c : V ⟶ M), b ≫ a = c ≫ a →
    restrict hG b F = restrict hG c F

/-- A restricted global family satisfies ordinary matching. -/
theorem isMatchingAlong_restrict (hG : IsReductive G) (a : M ⟶ T)
    (F : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G)) :
    IsMatchingAlong hG a (restrict hG a F) := by
  intro V b c h
  rw [restrict_comp, restrict_comp, h]

/-- Ordinary restriction matching gives the all-test overlap equality needed
for effective descent, with the direct/iterated ambient comparison included. -/
theorem overlap_range_eq_of_isMatchingAlong (hG : IsReductive G) (a : M ⟶ T)
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (hF : IsMatchingAlong hG a F) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (fst a.left)).map
          ((parabolicRepresentative F).hom ≫
            (pullbackComparison T.hom a.left M.hom (Over.w a) G).inv) ≫
          (canonicalOverlap a.left ((GroupScheme.baseChange T.hom).obj G)).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (snd a.left)).map
          ((parabolicRepresentative F).hom ≫
            (pullbackComparison T.hom a.left M.hom (Over.w a) G).inv)) := by
  apply HomScheme.TorusChartDescent.overlap_range_eq_of_evaluate_eq
    a.left T.hom (Over.w a) (parabolicRepresentative F).hom
  intro V b c h
  have hbc : b ≫ a = c ≫ a := Over.OverMorphism.ext h
  have he := congrArg Subtype.val (hF V b c hbc)
  rw [restrict_eq_evaluate hG F (parabolicRepresentative F).hom
      (parabolicRepresentative F).represents.2 b,
    restrict_eq_evaluate hG F (parabolicRepresentative F).hom
      (parabolicRepresentative F).represents.2 c] at he
  exact he

section

variable (hG : IsReductive G) (a : M ⟶ T)
    [IsAffine T.left] [IsAffine M.left] [Etale a.left] [Surjective a.left]
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (hF : IsMatchingAlong hG a F)

/-- Construct an actual global parabolic family from ordinarily matching
local data over an affine surjective étale parameter map. -/
def matchingAffineEtale : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G) :=
  descendAffineEtale a.left (hG.baseChange T.hom)
    ((parabolicRepresentative F).parabolic.comp_iso
      (pullbackComparison T.hom a.left M.hom (Over.w a) G).symm)
    (overlap_range_eq_of_isMatchingAlong hG a F hF)

/-- The constructed descent restricts to the original actual local family. -/
theorem restrict_matchingAffineEtale :
    restrict hG a (matchingAffineEtale hG a F hF) = F := by
  apply Subtype.ext
  rw [restrict_val_eq]
  unfold matchingAffineEtale
  rw [descendAffineEtale_baseChange, SubgroupFunctor.range_comp_iso,
    (parabolicRepresentative F).represents.2, ← SubgroupFunctor.comap_comp]
  simp only [Iso.symm_inv, Iso.inv_hom_id, SubgroupFunctor.comap_id]

include hF in
/-- Ordinary matching over an affine surjective étale parameter map has a
unique actual parabolic-family descent. -/
theorem existsUnique_restrict_affineEtale :
    ∃! H : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G),
      restrict hG a H = F := by
  refine ⟨matchingAffineEtale hG a F hF,
    restrict_matchingAffineEtale hG a F hF, ?_⟩
  intro H hH
  exact restrict_injective hG a (hH.trans
    (restrict_matchingAffineEtale hG a F hF).symm)

end

end Langlands.GroupScheme.ParabolicSubgroupModuli
