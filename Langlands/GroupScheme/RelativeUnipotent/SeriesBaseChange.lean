import Langlands.GroupScheme.RelativeUnipotent.VectorBundleBaseChangeCocycle
import Langlands.AlgebraicGeometry.PullbackFiniteLocalBasisRankProof
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Base change of finite vector-bundle series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeUnipotent

variable {S T : Scheme.{u}} (b : T ⟶ S)

/-- The exact finite-local-basis predicate is preserved by actual module pullback. -/
theorem IsFiniteLocallyFree.pullback {M : S.Modules} (h : IsFiniteLocallyFree M) :
    IsFiniteLocallyFree ((Scheme.Modules.pullback b).obj M) :=
  (Langlands.Scheme.Modules.pullbackFiniteLocalBasisRank T S b M).1 h

/-- An actual vector-bundle additive group remains one after arbitrary base change. -/
theorem IsVectorBundleAdditive.baseChange {V : GroupScheme S}
    (h : IsVectorBundleAdditive V) :
    IsVectorBundleAdditive ((GroupScheme.baseChange b).obj V) := by
  obtain ⟨hAffine, hSmooth, M, hM, e, he⟩ := h
  refine ⟨(show IsAffineHom (Limits.pullback.snd V.X.hom b) from
      MorphismProperty.pullback_snd _ _ hAffine),
    (show Smooth (Limits.pullback.snd V.X.hom b) from
      MorphismProperty.pullback_snd _ _ hSmooth),
    (Scheme.Modules.pullback b).obj M, hM.pullback b,
    baseChangeSectionPointsEquiv b M e, ?_⟩
  intro Z W a x
  exact baseChangeSectionPointsEquiv_naturality b M e he a x

/-- Arbitrary base change preserves a vector-bundle normal series and its length. -/
theorem HasVectorBundleSeries.baseChange {H : GroupScheme S} {n : ℕ}
    (h : HasVectorBundleSeries n H) :
    HasVectorBundleSeries n ((GroupScheme.baseChange b).obj H) := by
  induction n generalizing H with
  | zero =>
    change SubgroupFunctor.range (𝟙 H) = ⊥ at h
    have hb := congrArg (fun F : SubgroupFunctor H => F.baseChange b) h
    rw [← SubgroupFunctor.range_baseChangeHom, CategoryTheory.Functor.map_id,
      SubgroupFunctor.bot_baseChange] at hb
    exact hb
  | succ n ih =>
    obtain ⟨K, V, j, q, hj, hsmooth, hnormal, hquot, hvector, hseries⟩ := h
    refine ⟨(GroupScheme.baseChange b).obj K, (GroupScheme.baseChange b).obj V,
      (GroupScheme.baseChange b).map j, (GroupScheme.baseChange b).map q,
      hj.baseChange b,
      (show Smooth (Limits.pullback.snd K.X.hom b) from
        MorphismProperty.pullback_snd _ _ hsmooth), ?_, ?_,
      hvector.baseChange b, ih hseries⟩
    · rw [SubgroupFunctor.range_baseChangeHom]
      exact SubgroupFunctor.IsNormal.baseChange b hnormal
    · simpa only [SubgroupFunctor.range_baseChangeHom] using hquot.baseChange b

/-- Existence of a finite vector-bundle series is preserved by arbitrary base change. -/
theorem HasFiniteVectorBundleSeries.baseChange {H : GroupScheme S}
    (h : HasFiniteVectorBundleSeries H) :
    HasFiniteVectorBundleSeries ((GroupScheme.baseChange b).obj H) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.baseChange b⟩

/-- Pull back a length-and-proof witness, preserving its chosen length. -/
def seriesWitnessBaseChange {H : GroupScheme S}
    (w : {n : ℕ // HasVectorBundleSeries n H}) :
    {n : ℕ // HasVectorBundleSeries n ((GroupScheme.baseChange b).obj H)} :=
  ⟨w.val, w.property.baseChange b⟩

@[simp] lemma seriesWitnessBaseChange_val {H : GroupScheme S}
    (w : {n : ℕ // HasVectorBundleSeries n H}) :
    (seriesWitnessBaseChange b w).val = w.val := rfl

end Langlands.GroupScheme.RelativeUnipotent
