import Langlands.Geometry.Analytic.EtalePointwiseLifting.LocalizedStability
import Langlands.Geometry.Analytic.LocalizedEtalePullbackPoints
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-! # The ordinary étale pretopology of an analytic space -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

section Over

variable {C : Type*} [Category* C] {P : MorphismProperty C} {X : C}

/-- The analytic pullback property of the left square gives the full over-category limit. -/
theorem isPullback_over_of_left {W A B U : P.Over ⊤ X}
    {p : W ⟶ A} {q : W ⟶ B} {f : A ⟶ U} {g : B ⟶ U}
    (h : IsPullback p.left q.left f.left g.left) : IsPullback p q f g := by
  have w : p ≫ f = q ≫ g := MorphismProperty.Over.Hom.ext h.w
  let lift (s : PullbackCone f g) : s.pt ⟶ W := by
    have hs : s.fst.left ≫ f.left = s.snd.left ≫ g.left :=
      congrArg (fun k : s.pt ⟶ U => k.left) s.condition
    refine MorphismProperty.Over.homMk (h.lift _ _ hs) ?_
    rw [← MorphismProperty.Over.w p, h.lift_fst_assoc, MorphismProperty.Over.w]
  have hfst (s : PullbackCone f g) : lift s ≫ p = s.fst :=
    MorphismProperty.Over.Hom.ext (h.lift_fst _ _ _)
  have hsnd (s : PullbackCone f g) : lift s ≫ q = s.snd :=
    MorphismProperty.Over.Hom.ext (h.lift_snd _ _ _)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w lift hfst hsnd ?_)
  intro s m hm hn
  apply MorphismProperty.Over.Hom.ext
  apply h.hom_ext
  · exact congrArg (fun k : s.pt ⟶ A => k.left) (hm.trans (hfst s).symm)
  · exact congrArg (fun k : s.pt ⟶ B => k.left) (hn.trans (hsnd s).symm)

/-- An analytic pullback with a suitable structure morphism is a full over-object. -/
theorem exists_overPullback_of_left {A B U : P.Over ⊤ X}
    (f : A ⟶ U) (g : B ⟶ U) {R : C} {p : R ⟶ A.left} {q : R ⟶ B.left}
    (h : IsPullback p q f.left g.left) (hR : P (q ≫ B.hom)) :
    ∃ (W : P.Over ⊤ X) (p' : W ⟶ A) (q' : W ⟶ B),
      IsPullback p'.left q'.left f.left g.left := by
  have hp : p ≫ A.hom = q ≫ B.hom := by
    rw [← MorphismProperty.Over.w f, ← MorphismProperty.Over.w g,
      ← Category.assoc, ← Category.assoc, h.w]
  let W := MorphismProperty.Over.mk ⊤ (q ≫ B.hom) hR
  exact ⟨W, MorphismProperty.Over.homMk p hp, MorphismProperty.Over.homMk q rfl, h⟩

end Over

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (X : LocalizedCategory.{u, v, v} (K := K))

namespace EtaleSite

section
variable {K X}

/-- A morphism over an étale base object is étale as an analytic arrow. -/
theorem etale_left {U V : EtaleSite X} (f : U ⟶ V) : etale f.left := by
  let := (localizedEtaleStability (K := K)).2
  exact (etale (K := K)).of_postcomp f.left V.hom V.prop ((MorphismProperty.Over.w f).symm ▸ U.prop)

end

/-- Every étale-site cospan has a pullback computed on analytic spaces. -/
theorem exists_analyticPullback {U V W : EtaleSite X} (f : U ⟶ W) (g : V ⟶ W) :
    ∃ (T : EtaleSite X) (p : T ⟶ U) (q : T ⟶ V),
      IsPullback p.left q.left f.left g.left := by
  obtain ⟨T, p, q, hT, hq⟩ := localizedEtalePullbackBaseChange f.left g.left (etale_left f)
  exact exists_overPullback_of_left f g hT (etale_comp hq V.prop)

instance etaleSite_hasPullbacks : HasPullbacks (EtaleSite X) :=
  @hasPullbacks_of_hasLimit_cospan _ _ (fun {_ _ _ f g} => by
    obtain ⟨T, p, q, h⟩ := exists_analyticPullback K X f g
    exact (isPullback_over_of_left h).hasPullback)

/-- An étale-site pullback has the analytic pullback property on its left square. -/
theorem isPullback_left {T U V W : EtaleSite X}
    {p : T ⟶ U} {q : T ⟶ V} {f : U ⟶ W} {g : V ⟶ W} (h : IsPullback p q f g) :
    IsPullback p.left q.left f.left g.left := by
  let F := MorphismProperty.Over.forget (etale (K := K)) ⊤ X ⋙ Over.forget X
  obtain ⟨T', p', q', hT'⟩ := exists_analyticPullback K X f g
  have hT := isPullback_over_of_left hT'
  have hF : IsPullback (F.map p') (F.map q') (F.map f) (F.map g) := hT'
  let : PreservesLimit (cospan f g) F := preservesLimit_of_preserves_limit_cone hT.isLimit
    ((isLimitMapConePullbackConeEquiv F hT.w).symm hF.isLimit)
  exact h.map F

end EtaleSite

instance etalePrecoverage_isStableUnderBaseChange : (etalePrecoverage X).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} U V f hf W g P p q hp := by
    rw [ofArrows_mem_etalePrecoverage_iff] at hf ⊢
    intro x
    obtain ⟨i, y, hy⟩ := hf ((EtaleSite.points X).map g x)
    obtain ⟨z, _, hz⟩ := exists_point_of_isPullback_of_etale
      (EtaleSite.isPullback_left K X (hp i)).flip (EtaleSite.etale_left (f i)) y x hy
    exact ⟨i, z, hz⟩

/-- Jointly surjective families form the ordinary analytic étale pretopology. -/
def etalePretopology : Pretopology (EtaleSite X) :=
  (etalePrecoverage X).toPretopology

/-- This pretopology generates the ordinary analytic étale topology. -/
theorem etalePretopology_toGrothendieck : (etalePretopology K X).toGrothendieck = etaleTopology X :=
  (etalePrecoverage X).toGrothendieck_toPretopology_eq_toGrothendieck

end Langlands.Analytic.SaturatedAtlasPresentation
