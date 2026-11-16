import Langlands.GroupScheme.RelativeLevi.ParabolicPresheaf
import Langlands.GroupScheme.HomScheme.RelativeGraphRecovery

/-! # Coherent pullback of chosen actual parabolic representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M T U : Over S}

/-- The source comparison for family evaluation is the standard group
base-change composition comparison in the reverse direction. -/
lemma familySourceComparison_eq_baseChangeCompIso_symm
    (K : GroupScheme M.left) (a : T ⟶ M) (b : U ⟶ T) :
    familySourceComparison K a b = (baseChangeCompIso a.left b.left K).symm := by
  simp [familySourceComparison, Descent.pullbackComparison]

end Langlands.GroupScheme.TorusSubgroupModuli

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M T U : Over S}

/-- The unique inclusion-compatible comparison from the actual pullback of a
chosen representative to the chosen representative of the restricted subgroup. -/
def parabolicRepresentativePullbackIso (hG : IsReductive G) (a : T ⟶ M)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G))
    (F' : ParabolicSubgroup ((baseChange T.hom).obj G))
    (h : restrict hG a F = F') :
    (baseChange a.left).obj (parabolicRepresentative F).group ≅
      (parabolicRepresentative F').group :=
  (show F'.val.IsRepresentedBy (familyHom (parabolicRepresentative F).hom a) from
    ⟨(isRelativeParabolicSubgroup_familyHom hG _
      (parabolicRepresentative F).parabolic a).mono, congrArg Subtype.val h⟩
    ).isoOfIsRepresentedBy (parabolicRepresentative F').represents

/-- The comparison preserves the actual inclusion into the ambient group. -/
@[reassoc]
lemma parabolicRepresentativePullbackIso_hom_comp (hG : IsReductive G)
    (a : T ⟶ M) (F : ParabolicSubgroup ((baseChange M.hom).obj G))
    (F' : ParabolicSubgroup ((baseChange T.hom).obj G))
    (h : restrict hG a F = F') :
    (parabolicRepresentativePullbackIso hG a F F' h).hom ≫
        (parabolicRepresentative F').hom =
      familyHom (parabolicRepresentative F).hom a :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- Inclusion compatibility determines the chosen pullback comparison. -/
lemma parabolicRepresentativePullbackIso_unique (hG : IsReductive G)
    (a : T ⟶ M) (F : ParabolicSubgroup ((baseChange M.hom).obj G))
    (F' : ParabolicSubgroup ((baseChange T.hom).obj G))
    (h : restrict hG a F = F')
    (e : (baseChange a.left).obj (parabolicRepresentative F).group ≅
      (parabolicRepresentative F').group)
    (he : e.hom ≫ (parabolicRepresentative F').hom =
      familyHom (parabolicRepresentative F).hom a) :
    e = parabolicRepresentativePullbackIso hG a F F' h := by
  apply Iso.ext
  apply (parabolicRepresentative F').represents.hom_ext
  rw [he, parabolicRepresentativePullbackIso_hom_comp]

/-- Identity restriction gives the actual group identity pullback comparison. -/
@[simp]
lemma parabolicRepresentativePullbackIso_id (hG : IsReductive G)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G)) :
    parabolicRepresentativePullbackIso hG (𝟙 M) F F (restrict_id hG F) =
      baseChangeIdIso (parabolicRepresentative F).group := by
  symm
  apply parabolicRepresentativePullbackIso_unique hG (𝟙 M) F F (restrict_id hG F)
  exact (familyHom_id _).symm

/-- Pullback along a composite agrees with successive chosen representative
comparisons and the actual group base-change composition comparison. -/
lemma parabolicRepresentativePullbackIso_comp (hG : IsReductive G)
    (a : T ⟶ M) (b : U ⟶ T)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G))
    (F' : ParabolicSubgroup ((baseChange T.hom).obj G))
    (F'' : ParabolicSubgroup ((baseChange U.hom).obj G))
    (ha : restrict hG a F = F') (hb : restrict hG b F' = F'')
    (hab : restrict hG (b ≫ a) F = F'') :
    parabolicRepresentativePullbackIso hG (b ≫ a) F F'' hab =
      baseChangeCompIso a.left b.left (parabolicRepresentative F).group ≪≫
        (baseChange b.left).mapIso (parabolicRepresentativePullbackIso hG a F F' ha) ≪≫
          parabolicRepresentativePullbackIso hG b F' F'' hb := by
  symm
  apply parabolicRepresentativePullbackIso_unique hG (b ≫ a) F F'' hab
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    parabolicRepresentativePullbackIso_hom_comp]
  rw [← familyHom_comp, parabolicRepresentativePullbackIso_hom_comp,
    familyHom_evaluate_comp, familySourceComparison_eq_baseChangeCompIso_symm]
  simp

end Langlands.GroupScheme.ParabolicSubgroupModuli
