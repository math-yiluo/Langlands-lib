import Langlands.Geometry.Analytic.LocalizedEtalePullbackPoints
import Langlands.Geometry.Analytic.QuasiEtaleBaseChangeReduction
import Langlands.Sheaf.Equivariant.AnalyticEtaleInvariantPullback
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Base change on small analytic étale sites -/

noncomputable section

universe u v a b

namespace Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Langlands.Sheaf (HasImagePullbacks)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)} (f : X ⟶ Y)

local instance etaleHasPullbacksAlong : (etale (K := K)).HasPullbacksAlong f where
  hasPullback g hg := by
    obtain ⟨P, p, q, hpq, _⟩ := localizedEtalePullbackBaseChange g f hg
    exact hpq.hasPullback

local instance etaleStableUnderBaseChange :
    (etale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderBaseChange :=
  localizedEtaleBaseChange

/-- Base change pulls each étale object over `Y` back along `f`. -/
abbrev baseChange : EtaleSite Y ⥤ EtaleSite X := MorphismProperty.Over.pullback etale ⊤ f

/-- The projection of a base changed étale object to the original analytic space. -/
abbrev baseChangeProjection (U : EtaleSite Y) : ((baseChange f).obj U).left ⟶ U.left :=
  pullback.fst U.hom f

/-- The structure map and the projection exhibit the base changed object as a pullback. -/
theorem baseChange_isPullback (U : EtaleSite Y) :
    IsPullback (baseChangeProjection f U) ((baseChange f).obj U).hom U.hom f :=
  IsPullback.of_hasPullback _ _

/-- Projection to the original analytic space is natural on analytic étale objects. -/
theorem baseChange_map_projection {U V : EtaleSite Y} (g : U ⟶ V) :
    ((baseChange f).map g).left ≫ baseChangeProjection f V =
      baseChangeProjection f U ≫ g.left := by
  change pullback.lift (pullback.fst U.hom f ≫ g.left) (pullback.snd U.hom f) _ ≫
    pullback.fst V.hom f = _
  exact pullback.lift_fst _ _ _

/-- The naturality square for the base change projections is a pullback. -/
theorem baseChange_map_isPullback {U V : EtaleSite Y} (g : U ⟶ V) :
    IsPullback ((baseChange f).map g).left (baseChangeProjection f U)
      (baseChangeProjection f V) g.left := by
  have h := (baseChange_isPullback f U).flip
  rw [← MorphismProperty.Over.w g, ← MorphismProperty.Over.w ((baseChange f).map g)] at h
  exact h.of_right (baseChange_map_projection f g) (baseChange_isPullback f V).flip

private theorem baseChange_hasImagePullbacks : HasImagePullbacks (baseChange f) := by
  intro W U V g h
  obtain ⟨P, p, q, hpq, hq⟩ := localizedEtalePullbackBaseChange g.left h.left (etale_left g)
  let T : EtaleSite Y := MorphismProperty.Over.mk ⊤ (q ≫ V.hom) (etale_comp hq V.prop)
  have hp : p ≫ U.hom = q ≫ V.hom := by
    rw [← MorphismProperty.Over.w g, ← MorphismProperty.Over.w h,
      ← Category.assoc, ← Category.assoc, hpq.w]
  let p₀ : T ⟶ U := MorphismProperty.Over.homMk p hp
  let q₀ : T ⟶ V := MorphismProperty.Over.homMk q rfl
  have hcomm : p₀ ≫ g = q₀ ≫ h := MorphismProperty.Over.Hom.ext hpq.w
  refine ⟨T, p₀, q₀, hcomm, ?_⟩
  apply IsPullback.of_map_of_faithful
    (F := MorphismProperty.Over.forget etale ⊤ X ⋙ Over.forget X)
  have hsource : IsPullback p₀.left q₀.left g.left h.left := hpq
  have hout := (baseChange_map_isPullback f p₀).paste_vert hsource
  rw [← baseChange_map_projection f q₀, ← baseChange_map_projection f g] at hout
  have hm := congrArg (fun m => ((baseChange f).map m).left) hcomm
  rw [Functor.map_comp, Functor.map_comp] at hm
  exact hout.of_bot hm (baseChange_map_isPullback f h)

/-- Base change along any analytic map preserves jointly surjective étale covering families. -/
theorem baseChange_coverPreservingPrecoverage :
    etalePrecoverage Y ≤ (etalePrecoverage X).comap (baseChange f) := by
  intro U R hR
  obtain ⟨I, V, g, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows, ofArrows_mem_etalePrecoverage_iff]
  have hCover := (ofArrows_mem_etalePrecoverage_iff (V := V) (f := g)).mp hR
  intro x
  obtain ⟨i, y, hy⟩ := hCover (localizedSpaceFunctor.map (baseChangeProjection f U) x)
  obtain ⟨z, _, hz⟩ := exists_point_of_isPullback_of_etale
    (baseChange_map_isPullback f (g i)).flip (etale_left (g i)) y x hy
  exact ⟨i, z, hz⟩

/-- Small analytic étale base change is continuous for the ordinary étale topologies. -/
instance baseChange_isContinuous : (baseChange f).IsContinuous (etaleTopology Y) (etaleTopology X) :=
  (baseChange_hasImagePullbacks f).isContinuous _ _ (baseChange_coverPreservingPrecoverage f)

variable (A : Type a) [Category.{b} A]

/-- Direct image along an analytic map evaluates on base changed étale objects. -/
def baseChangeDirectImage : Sheaf (etaleTopology X) A ⥤ Sheaf (etaleTopology Y) A :=
  (baseChange f).sheafPushforwardContinuous A (etaleTopology Y) (etaleTopology X)

/-- For an étale map of bases, ordinary restriction is left adjoint to direct image. -/
def postcomposeEtaleAdjunction (hf : etale f) :
    (postcomposeEtale hf).sheafPushforwardContinuous A (etaleTopology X) (etaleTopology Y) ⊣
      baseChangeDirectImage f A :=
  (MorphismProperty.Over.mapPullbackAdj etale ⊤ f hf trivial).sheafPushforwardContinuous
    (etaleTopology X) (etaleTopology Y)

section InverseImage

variable [HasWeakSheafify (etaleTopology X) A]
  [∀ P : (EtaleSite Y)ᵒᵖ ⥤ A, (baseChange f).op.HasLeftKanExtension P]

/-- Inverse image is the sheafification of the left Kan extension along étale base change. -/
def baseChangeInverseImage : Sheaf (etaleTopology Y) A ⥤ Sheaf (etaleTopology X) A :=
  Functor.sheafPullbackConstruction.sheafPullback (baseChange f) A
    (etaleTopology Y) (etaleTopology X)

/-- The analytic inverse image is left adjoint to direct image. -/
def baseChangeAdjunction : baseChangeInverseImage f A ⊣ baseChangeDirectImage f A :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (baseChange f) A
    (etaleTopology Y) (etaleTopology X)

end InverseImage

end Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite
