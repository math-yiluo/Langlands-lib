import Langlands.Geometry.Analytic.CompactQuasiEtalePullbacks
import Langlands.Geometry.Analytic.CompactPullbackActionContinuity
import Langlands.CategoryTheory.PullbackActions

/-! # Compact continuous pullbacks from explicit geometric prerequisites -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}

/-- The full localized pullback universal property restricts to the actual
quasi-étale site, with no condition on the analytic test object's compactness. -/
def quasiEtalePullbackIsLimit {B U V : QuasiEtaleSite X} {f : U ⟶ B} {g : V ⟶ B}
    (t : PullbackCone f g) (ht : IsPullback t.fst.left t.snd.left f.left g.left) :
    IsLimit t :=
  PullbackCone.isLimitAux' t (fun s => by
    let w : s.fst.left ≫ f.left = s.snd.left ≫ g.left :=
      congrArg (fun k => k.left) s.condition
    let l : s.pt ⟶ t.pt := MorphismProperty.Over.homMk
      (ht.lift s.fst.left s.snd.left w) (by
        rw [← MorphismProperty.Over.w t.fst, ← Category.assoc, ht.lift_fst]
        exact MorphismProperty.Over.w s.fst)
    refine ⟨l, ?_, ?_, ?_⟩
    · apply MorphismProperty.Over.Hom.ext
      exact ht.lift_fst _ _ _
    · apply MorphismProperty.Over.Hom.ext
      exact ht.lift_snd _ _ _
    · intro m hm₁ hm₂
      apply MorphismProperty.Over.Hom.ext
      apply ht.hom_ext
      · exact (congrArg (fun k => k.left) hm₁).trans (ht.lift_fst _ _ _).symm
      · exact (congrArg (fun k => k.left) hm₂).trans (ht.lift_snd _ _ _).symm)

variable {G : Type z} [Group G] [TopologicalSpace G]
  {B U V : QuasiEtaleSite X} (f : U ⟶ B) (g : V ⟶ B)
  (σU : G →* Aut U.left) (σV : G →* Aut V.left)

/-- A compact site pullback carrying a continuous action with full projection
equivariance for the specified source actions. -/
structure CompactContinuousPullbackData where
  cone : PullbackCone f g
  isLimit : IsLimit cone
  compact : IsCompactSpace cone.pt.left
  action : G →* Aut cone.pt.left
  continuous : IsContinuousAction action
  fst_equivariant : ∀ a, (action a).hom ≫ cone.fst.left = cone.fst.left ≫ (σU a).hom
  snd_equivariant : ∀ a, (action a).hom ≫ cone.snd.left = cone.snd.left ≫ (σV a).hom

/-- Combine actual compact pullback existence, its categorical induced action,
and the explicit pullback-continuity prerequisite. -/
def compactContinuousPullback
    (hgeom : CompactQuasiEtalePullbacksStatement.{u, v} (K := K))
    (hcont : CompactPullbackActionContinuityStatement.{u, v, z} (K := K) (G := G))
    (hB : IsCompactSpace B.left) (hU : IsCompactSpace U.left)
    (hV : IsCompactSpace V.left) (σB : G →* Aut B.left)
    (hσU : IsContinuousAction σU) (hσV : IsContinuousAction σV)
    (hf : ∀ a, (σU a).hom ≫ f.left = f.left ≫ (σB a).hom)
    (hg : ∀ a, (σV a).hom ≫ g.left = g.left ≫ (σB a).hom) :
    CompactContinuousPullbackData f g σU σV := by
  let hex := hgeom X B U V f g hB hU hV
  let t := Classical.choose hex
  have ht := Classical.choose_spec hex
  let σ := Langlands.CategoricalPullback.pullbackAction ht.2 σU σV σB hf hg
  exact {
    cone := t
    isLimit := quasiEtalePullbackIsLimit t ht.2
    compact := ht.1
    action := σ
    continuous := hcont B.left U.left V.left t.pt.left f.left g.left
      t.fst.left t.snd.left hB hU hV ht.1 ht.2 σ σU σV hσU hσV
      (Langlands.CategoricalPullback.pullbackAction_fst ht.2 σU σV σB hf hg)
      (Langlands.CategoricalPullback.pullbackAction_snd ht.2 σU σV σB hf hg)
    fst_equivariant := Langlands.CategoricalPullback.pullbackAction_fst ht.2 σU σV σB hf hg
    snd_equivariant := Langlands.CategoricalPullback.pullbackAction_snd ht.2 σU σV σB hf hg
  }

end Langlands.Analytic.SaturatedAtlasPresentation
