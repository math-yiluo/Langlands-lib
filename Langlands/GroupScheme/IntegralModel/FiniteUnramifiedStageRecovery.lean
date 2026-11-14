import Langlands.GroupScheme.IntegralModel.FiniteUnramifiedStage
import Langlands.GroupScheme.IntegralModel.BaseChange

/-! # Exact generic recovery of finite unramified integral stages -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000

namespace Langlands.GroupScheme.Descent.FiniteUnramified

@[reassoc] private theorem map_fst {S T : Scheme.{u}} (p : T ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange p).map f).hom.hom.left ≫ pullback.fst H.X.hom p =
      pullback.fst G.X.hom p ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

private theorem hom_ext_twice {S T U : Scheme.{u}} (f : T ⟶ S) (q : U ⟶ T)
    (H : GroupScheme S) {P : GroupScheme U}
    {a b : P ⟶ (baseChange q).obj ((baseChange f).obj H)}
    (h : a.hom.hom.left ≫ pullback.fst ((baseChange f).obj H).X.hom q ≫
        pullback.fst H.X.hom f =
      b.hom.hom.left ≫ pullback.fst ((baseChange f).obj H).X.hom q ≫
        pullback.fst H.X.hom f) : a = b := by
  apply (cancel_mono (pullbackComparison f q (q ≫ f) rfl H).hom).mp
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      pullbackComparison_hom_fst] using h
  · exact (Over.w (a ≫ (pullbackComparison f q (q ≫ f) rfl H).hom).hom.hom).trans
      (Over.w (b ≫ (pullbackComparison f q (q ≫ f) rfl H).hom).hom.hom).symm

private theorem comparison_tower {S T U V : Scheme.{u}}
    (f : T ⟶ S) (q : U ⟶ T) (p : V ⟶ U)
    (r : U ⟶ S) (t : V ⟶ S) (k : V ⟶ T)
    (hq : q ≫ f = r) (hp : p ≫ r = t) (hk : k ≫ f = t)
    (h : p ≫ q = k) (H : GroupScheme S) :
    (baseChange p).mapIso (pullbackComparison f q r hq H) ≪≫
        pullbackComparison r p t hp H =
      pullbackComparison q p k h ((baseChange f).obj H) ≪≫
        pullbackComparison f k t hk H := by
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Grp.comp_hom_hom,
      Over.comp_left, Category.assoc, pullbackComparison_hom_fst,
      map_fst_assoc, pullbackComparison_hom_fst_assoc]
  · exact (Over.w (((baseChange p).mapIso (pullbackComparison f q r hq H) ≪≫
      pullbackComparison r p t hp H).hom.hom.hom)).trans
      (Over.w ((pullbackComparison q p k h ((baseChange f).obj H) ≪≫
        pullbackComparison f k t hk H).hom.hom.hom)).symm

private theorem recovery_square {C : Type*} [Category C]
    {X Y Z P Q P' Q' T : C}
    (u : X ≅ Y) (d : Z ≅ Y) (n : Z ≅ T) (s : Y ≅ Q) (c : P ≅ T)
    (j : X ≅ Q') (a : P' ≅ Q') (g : P' ≅ P) (h : Q' ≅ Q) (b : P' ≅ T)
    (hc : u ≪≫ s = j ≪≫ h) (hg : g ≪≫ c = b)
    (ha : g.symm ≪≫ a ≪≫ h = c ≪≫ n.symm ≪≫ d ≪≫ s) :
    u ≪≫ d.symm ≪≫ n = j ≪≫ a.symm ≪≫ b := by
  have hi := congrArg CategoryTheory.Iso.inv ha
  have hj := congrArg CategoryTheory.Iso.hom hc
  have hb := congrArg CategoryTheory.Iso.hom hg
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc] at hi
  simp only [Iso.trans_hom] at hj hb
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    u.hom ≫ d.inv ≫ n.hom =
        (u.hom ≫ s.hom) ≫ (s.inv ≫ d.inv ≫ n.hom ≫ c.inv) ≫ c.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (j.hom ≫ h.hom) ≫ (h.inv ≫ a.inv ≫ g.hom) ≫ c.hom := by rw [hj, ← hi]
    _ = j.hom ≫ a.inv ≫ b.hom := by
      simp only [← hb, Category.assoc, Iso.hom_inv_id_assoc]

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance stageRecoveryNormedField : NontriviallyNormedField F := localNormedField F
local instance stageRecoveryUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance stageRecoveryComplete : CompleteSpace F := localNormedField_complete F

/-- Generic comparisons commute with enlargement of the finite integer stage. -/
theorem inertiaGenericSquare_enlargement
    {E E' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') (hE : E ≤ inertiaFixedField F) (hE' : E' ≤ inertiaFixedField F)
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F E)))) :
    (baseChange (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).mapIso
        (stageIntegralComparison F h hE hE' H) ≪≫ inertiaGenericSquare F E hE H =
      inertiaGenericSquare F E' hE' ((baseChange (stageIntegerMap F h)).obj H) ≪≫
        (baseChange (fieldSpecMap F hE')).mapIso (enlargementGenericSquare F h H) ≪≫
          pullbackComparison (fieldSpecMap F h) (fieldSpecMap F hE')
            (fieldSpecMap F hE) (fieldSpecMap_comp F h hE')
            ((baseChange (Spec.algebraMap (extensionIntegers F E) E)).obj H) := by
  apply Iso.ext
  apply hom_ext_twice (Spec.algebraMap (extensionIntegers F E) E)
    (fieldSpecMap F hE) H
  simp only [Iso.trans_hom, Functor.mapIso_hom, Grp.comp_hom_hom,
    Over.comp_left, Category.assoc, inertiaGenericSquare_fst,
    pullbackComparison_hom_fst_assoc, map_fst_assoc,
    enlargementGenericSquare_fst, stageIntegralComparison_fst,
    inertiaGenericSquare_fst_assoc]


section RawRecovery

variable {G : GroupScheme (Spec (CommRingCat.of F))}
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      ((baseChange (Spec.algebraMap F (inertiaFixedField F))).obj G))
    (E E' : IntermediateField F (SeparableClosure F))
    (h : E ≤ E') (hE : E ≤ inertiaFixedField F) (hE' : E' ≤ inertiaFixedField F)
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F E))))
    (d : N.group ≅ (baseChange (spectralIntegerMap F E hE)).obj H)
    (a : (baseChange (fieldSpecMap F h)).obj ((baseChange (Spec.algebraMap F E)).obj G) ≅
      (baseChange (fieldSpecMap F h)).obj
        ((baseChange (Spec.algebraMap (extensionIntegers F E) E)).obj H))

/-- The generic identification at an explicit enlarged finite field. -/
def rawStageGenericIso :
    (baseChange (Spec.algebraMap (extensionIntegers F E') E')).obj
        ((baseChange (stageIntegerMap F h)).obj H) ≅
      (baseChange (Spec.algebraMap F E')).obj G :=
  enlargementGenericSquare F h H ≪≫ a.symm ≪≫
    pullbackComparison (Spec.algebraMap F E) (fieldSpecMap F h)
      (Spec.algebraMap F E') (fieldSpecMap_base F h) G

/-- Exact generic recovery at two explicit finite intermediate fields. -/
theorem rawStage_generic
    (ha : pullIso (fieldSpecMap F hE') (fieldSpecMap_comp F h hE')
      (fieldSpecMap_comp F h hE') a =
        pullbackComparison (Spec.algebraMap F E) (fieldSpecMap F hE)
          (Spec.algebraMap F (inertiaFixedField F)) (fieldSpecMap_base F hE) G ≪≫
          N.genericIso.symm ≪≫
            (baseChange (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).mapIso d ≪≫
              inertiaGenericSquare F E hE H) :
    (baseChange (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).map
        (stageIntegralComparison F h hE hE' H ≪≫ d.symm).hom ≫ N.genericIso.hom =
      (inertiaGenericSquare F E' hE' ((baseChange (stageIntegerMap F h)).obj H)).hom ≫
        (baseChange (fieldSpecMap F hE')).map
          (enlargementGenericSquare F h H ≪≫ a.symm ≪≫
            pullbackComparison (Spec.algebraMap F E) (fieldSpecMap F h)
              (Spec.algebraMap F E') (fieldSpecMap_base F h) G).hom ≫
          (pullbackComparison (Spec.algebraMap F E') (fieldSpecMap F hE')
            (Spec.algebraMap F (inertiaFixedField F)) (fieldSpecMap_base F hE') G).hom := by
  have hc := inertiaGenericSquare_enlargement F h hE hE' H
  have hf := comparison_tower (Spec.algebraMap F E) (fieldSpecMap F h) (fieldSpecMap F hE')
    (Spec.algebraMap F E') (Spec.algebraMap F (inertiaFixedField F))
    (fieldSpecMap F hE) (fieldSpecMap_base F h) (fieldSpecMap_base F hE')
    (fieldSpecMap_base F hE) (fieldSpecMap_comp F h hE') G
  have hr := recovery_square
    ((baseChange (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).mapIso
      (stageIntegralComparison F h hE hE' H))
    ((baseChange (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).mapIso d)
    N.genericIso (inertiaGenericSquare F E hE H)
    (pullbackComparison (Spec.algebraMap F E) (fieldSpecMap F hE)
      (Spec.algebraMap F (inertiaFixedField F)) (fieldSpecMap_base F hE) G)
    (inertiaGenericSquare F E' hE' ((baseChange (stageIntegerMap F h)).obj H) ≪≫
      (baseChange (fieldSpecMap F hE')).mapIso (enlargementGenericSquare F h H))
    ((baseChange (fieldSpecMap F hE')).mapIso a)
    (pullbackComparison (fieldSpecMap F h) (fieldSpecMap F hE') (fieldSpecMap F hE)
      (fieldSpecMap_comp F h hE') ((baseChange (Spec.algebraMap F E)).obj G))
    (pullbackComparison (fieldSpecMap F h) (fieldSpecMap F hE') (fieldSpecMap F hE)
      (fieldSpecMap_comp F h hE')
      ((baseChange (Spec.algebraMap (extensionIntegers F E) E)).obj H))
    ((baseChange (fieldSpecMap F hE')).mapIso
        (pullbackComparison (Spec.algebraMap F E) (fieldSpecMap F h)
          (Spec.algebraMap F E') (fieldSpecMap_base F h) G) ≪≫
      pullbackComparison (Spec.algebraMap F E') (fieldSpecMap F hE')
        (Spec.algebraMap F (inertiaFixedField F)) (fieldSpecMap_base F hE') G)
    (by simpa only [Iso.trans_assoc] using hc) hf.symm ha
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc] using congrArg CategoryTheory.Iso.hom hr


end RawRecovery

end Langlands.GroupScheme.Descent.FiniteUnramified
