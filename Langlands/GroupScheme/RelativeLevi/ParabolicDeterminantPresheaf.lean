import Langlands.GroupScheme.Lie.DeterminantBaseChangeCoherence
import Langlands.GroupScheme.RelativeLevi.ParabolicLieDeterminant
import Langlands.GroupScheme.RelativeLevi.ParabolicRepresentativePullback
import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleDual

/-! # The actual Lie determinant line bundle on parabolic families -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

private lemma determinantBaseChange_composition_forward
    {S T U : Scheme.{u}} (b : T ⟶ S) (c : U ⟶ T)
    (G : GroupScheme S) (hG : Smooth G.X.hom) :
    (LineBundle.pullback c).mapIso (smoothLieDeterminantBaseChangeIso b G hG) ≪≫
        smoothLieDeterminantBaseChangeIso c ((baseChange b).obj G)
          (smooth_baseChange_of_smooth b G hG) =
      (LineBundle.pullbackComp c b).app (smoothLieDeterminant G hG) ≪≫
        smoothLieDeterminantBaseChangeIso (c ≫ b) G hG ≪≫
        smoothLieDeterminantIso (smooth_baseChange_of_smooth (c ≫ b) G hG)
          (smooth_baseChange_of_smooth c ((baseChange b).obj G)
            (smooth_baseChange_of_smooth b G hG)) (baseChangeCompIso b c G) := by
  have h := congrArg (fun e => e ≪≫ smoothLieDeterminantIso
      (smooth_baseChange_of_smooth (c ≫ b) G hG)
      (smooth_baseChange_of_smooth c ((baseChange b).obj G)
        (smooth_baseChange_of_smooth b G hG)) (baseChangeCompIso b c G))
    (smoothLieDeterminantBaseChangeIso_composition b c G hG)
  simpa only [Iso.trans_assoc, smoothLieDeterminantIso_comp, Iso.symm_self_id,
    smoothLieDeterminantIso_refl, Iso.trans_refl] using h

namespace ParabolicSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M T U : Over S}

/-- The canonical pullback comparison for the actual determinants of chosen
parabolic representatives. -/
def parabolicLieDeterminantPullbackIso (hG : IsReductive G) (a : T ⟶ M)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G))
    (F' : ParabolicSubgroup ((baseChange T.hom).obj G))
    (h : restrict hG a F = F') :
    (LineBundle.pullback a.left).obj (parabolicRepresentative F).lieDeterminant ≅
      (parabolicRepresentative F').lieDeterminant :=
  smoothLieDeterminantBaseChangeIso a.left (parabolicRepresentative F).group
      (parabolicRepresentative F).parabolic.smooth ≪≫
    smoothLieDeterminantIso
      (smooth_baseChange_of_smooth a.left (parabolicRepresentative F).group
        (parabolicRepresentative F).parabolic.smooth)
      (parabolicRepresentative F').parabolic.smooth
      (parabolicRepresentativePullbackIso hG a F F' h)

lemma parabolicLieDeterminantPullbackIso_id (hG : IsReductive G)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G)) :
    parabolicLieDeterminantPullbackIso hG (𝟙 M) F F (restrict_id hG F) =
      (LineBundle.pullbackId M.left).app (parabolicRepresentative F).lieDeterminant := by
  dsimp only [parabolicLieDeterminantPullbackIso]
  rw [parabolicRepresentativePullbackIso_id]
  exact smoothLieDeterminantBaseChangeIso_identity _ _

lemma parabolicLieDeterminantPullbackIso_comp (hG : IsReductive G)
    (a : T ⟶ M) (b : U ⟶ T)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G))
    (F' : ParabolicSubgroup ((baseChange T.hom).obj G))
    (F'' : ParabolicSubgroup ((baseChange U.hom).obj G))
    (ha : restrict hG a F = F') (hb : restrict hG b F' = F'')
    (hab : restrict hG (b ≫ a) F = F'') :
    (LineBundle.pullback b.left).mapIso
        (parabolicLieDeterminantPullbackIso hG a F F' ha) ≪≫
      parabolicLieDeterminantPullbackIso hG b F' F'' hb =
    (LineBundle.pullbackComp b.left a.left).app (parabolicRepresentative F).lieDeterminant ≪≫
      parabolicLieDeterminantPullbackIso hG (b ≫ a) F F'' hab := by
  dsimp only [parabolicLieDeterminantPullbackIso]
  rw [Functor.mapIso_trans]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc ((LineBundle.pullback b.left).mapIso
    (smoothLieDeterminantIso
      (smooth_baseChange_of_smooth a.left (parabolicRepresentative F).group
        (parabolicRepresentative F).parabolic.smooth)
      (parabolicRepresentative F').parabolic.smooth
      (parabolicRepresentativePullbackIso hG a F F' ha))),
    smoothLieDeterminantBaseChangeIso_naturality]
  simp only [Iso.trans_assoc, smoothLieDeterminantIso_comp]
  rw [parabolicRepresentativePullbackIso_comp hG a b F F' F'' ha hb hab,
    ← smoothLieDeterminantIso_comp
      (smooth_baseChange_of_smooth (b.left ≫ a.left) (parabolicRepresentative F).group
        (parabolicRepresentative F).parabolic.smooth)
      (smooth_baseChange_of_smooth b.left
        ((baseChange a.left).obj (parabolicRepresentative F).group)
        (smooth_baseChange_of_smooth a.left (parabolicRepresentative F).group
          (parabolicRepresentative F).parabolic.smooth))
      (parabolicRepresentative F'').parabolic.smooth]
  simpa only [Iso.trans_assoc, ParabolicRepresentative.lieDeterminant, Over.comp_left] using
    congrArg (fun e => e ≪≫ smoothLieDeterminantIso
      (smooth_baseChange_of_smooth b.left
        ((baseChange a.left).obj (parabolicRepresentative F).group)
        (smooth_baseChange_of_smooth a.left (parabolicRepresentative F).group
          (parabolicRepresentative F).parabolic.smooth))
      (parabolicRepresentative F'').parabolic.smooth
      ((baseChange b.left).mapIso (parabolicRepresentativePullbackIso hG a F F' ha) ≪≫
        parabolicRepresentativePullbackIso hG b F' F'' hb))
      (determinantBaseChange_composition_forward a.left b.left
        (parabolicRepresentative F).group (parabolicRepresentative F).parabolic.smooth)

/-- The actual Lie determinant on all parabolic families, with coherent
canonical pullback comparisons. -/
def parabolicLieDeterminantPresheafLineBundle (G : GroupScheme S) (hG : IsReductive G) :
    PresheafLineBundle (parabolicPresheaf G hG) where
  bundle _ F := (parabolicRepresentative F).lieDeterminant
  pullbackIso a F F' h := parabolicLieDeterminantPullbackIso hG a F F' h
  pullbackIso_id _ F := parabolicLieDeterminantPullbackIso_id hG F
  pullbackIso_comp a b F F' F'' hb ha := by
    have h := congrArg
      (fun e => ((LineBundle.pullbackComp a.left b.left).app
        (parabolicRepresentative F).lieDeterminant).symm ≪≫ e)
      (parabolicLieDeterminantPullbackIso_comp hG b a F F' F'' hb ha
        ((restrict_comp hG b a F).symm.trans ((congrArg (restrict hG a) hb).trans ha)))
    simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using h.symm

@[simp]
lemma parabolicLieDeterminantPresheafLineBundle_bundle (hG : IsReductive G)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G)) :
    (parabolicLieDeterminantPresheafLineBundle G hG).bundle M F =
      (parabolicRepresentative F).lieDeterminant := rfl

/-- The dual of the actual Lie determinant on all parabolic families. -/
def parabolicLieDeterminantDualPresheafLineBundle (G : GroupScheme S)
    (hG : IsReductive G) : PresheafLineBundle (parabolicPresheaf G hG) :=
  (parabolicLieDeterminantPresheafLineBundle G hG).dual

@[simp]
lemma parabolicLieDeterminantDualPresheafLineBundle_bundle (hG : IsReductive G)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G)) :
    (parabolicLieDeterminantDualPresheafLineBundle G hG).bundle M F =
      (parabolicRepresentative F).lieDeterminant.dual := rfl

/-- Compare the coherent determinant line with the determinant of any actual
representative of the same parabolic family. -/
def parabolicLieDeterminantRepresentativeIso (hG : IsReductive G)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G)) (r : ParabolicRepresentative F) :
    (parabolicLieDeterminantPresheafLineBundle G hG).bundle M F ≅ r.lieDeterminant :=
  (parabolicRepresentative F).lieDeterminantChangeIso r

/-- Compare the coherent determinant dual with the determinant dual of any
actual representative of the same parabolic family. -/
def parabolicLieDeterminantDualRepresentativeIso (hG : IsReductive G)
    (F : ParabolicSubgroup ((baseChange M.hom).obj G)) (r : ParabolicRepresentative F) :
    (parabolicLieDeterminantDualPresheafLineBundle G hG).bundle M F ≅
      r.lieDeterminant.dual :=
  LineBundle.dualIso (parabolicLieDeterminantRepresentativeIso hG F r)

end ParabolicSubgroupModuli
end Langlands.GroupScheme
