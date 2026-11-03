import Langlands.Representation.Aubert.General.AlternatingOperator
import Mathlib.CategoryTheory.Whiskering

/-! # Exact-K0 term transitivity from actual normalized stage isomorphisms -/

noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace Langlands.Aubert.General

universe uG uV

open SmoothRep

private def inversePullbackIso {H K : Type uG} [Group H] [Group K]
    [TopologicalSpace H] [TopologicalSpace K] (e : H ≃ₜ* K) :
    (SmoothRep.pullbackFunctor.{uG, uG, uV} e.symm ⋙ SmoothRep.pullbackFunctor e) ≅
      𝟭 (SmoothRep.{0, uG, uV} ℂ H) :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun h => by
        ext a
        change A.representation (e.symm (e h)) a = A.representation h a
        rw [e.symm_apply_apply]))
    (fun _ => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      rfl)

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
  (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
  (hM : IsClosed (M₁ : Set G))
  (hMM : M₀ ≤ M₁)
  (hL : IsSemidirectDecomposition
    (P₀.subgroupOf M₁) (M₀.subgroupOf M₁) (U₀.subgroupOf M₁))
  (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))

/-- The actual four-functor term through the coarse Levi, retaining its
literal inner subgroup copy. -/
def stagedInductionJacquetFunctor :
    SmoothRep.{0, uG, max uG uV} ℂ G ⥤ SmoothRep.{0, uG, max uG uV} ℂ G :=
  letI := hM.locallyCompactSpace
  jacquetFunctor h₁ hU₁ ⋙
    jacquetFunctor hL (hU₀.preimage continuous_subtype_val) ⋙
    normalizedInductionFunctor hL (hU₀.preimage continuous_subtype_val) ⋙
    normalizedInductionFunctor h₁ hU₁

variable
  (hiStages :
    leviNormalizedInductionFunctor.{uG, max uG uV} hM hMM hL hU₀ ⋙
        normalizedInductionFunctor h₁ hU₁ ≅ normalizedInductionFunctor h₀ hU₀)
  (hrStages :
    jacquetFunctor.{uG, max uG uV} h₁ hU₁ ⋙
        leviNormalizedJacquetFunctor hM hMM hL hU₀ ≅ jacquetFunctor h₀ hU₀)

/-- Compose the actual two stage isomorphisms, cancelling the inverse canonical
pullbacks between the ambient and inner fine Levi. -/
def inductionJacquetStagesIso :
    stagedInductionJacquetFunctor.{uG, uV} h₁ hM hL hU₀ hU₁ ≅
      inductionJacquetFunctor.{uG, uV} h₀ hU₀ := by
  letI := hM.locallyCompactSpace
  let F := jacquetFunctor.{uG, max uG uV} h₁ hU₁ ⋙
    jacquetFunctor hL (hU₀.preimage continuous_subtype_val)
  let H := normalizedInductionFunctor.{uG, max uG uV}
    hL (hU₀.preimage continuous_subtype_val) ⋙
    normalizedInductionFunctor h₁ hU₁
  let e := subgroupOfContinuousEquiv hMM
  have hInsert :
      F ⋙ H ≅ (F ⋙
        (SmoothRep.pullbackFunctor e.symm ⋙ SmoothRep.pullbackFunctor e)) ⋙ H := by
    simpa only [Functor.comp_id] using
      (isoWhiskerRight (isoWhiskerLeft F (inversePullbackIso e).symm) H)
  exact hInsert ≪≫
    (isoWhiskerLeft (F ⋙ SmoothRep.pullbackFunctor e.symm) hiStages) ≪≫
    (isoWhiskerRight hrStages (normalizedInductionFunctor h₀ hU₀))

include hiStages hrStages in
/-- On the full exact finite-length Grothendieck group, the four actual maps
through the coarse Levi equal the direct fine term. -/
theorem inductionK0_comp_leviTerm_comp_jacquetK0
    (hfl₀ : ParabolicFiniteLength.{uG, max uG uV} h₀ hU₀)
    (hfl₁ : ParabolicFiniteLength.{uG, max uG uV} h₁ hU₁)
    (hflL : letI := hM.locallyCompactSpace
      ParabolicFiniteLength.{uG, max uG uV} hL (hU₀.preimage continuous_subtype_val)) :
    letI := hM.locallyCompactSpace
    (inductionK0 h₁ hU₁ hfl₁.1 hfl₁.2.1).comp
      (((inductionK0 hL (hU₀.preimage continuous_subtype_val) hflL.1 hflL.2.1).comp
          (jacquetK0 hL (hU₀.preimage continuous_subtype_val)
            hflL.2.2.1 hflL.2.2.2)).comp
        (jacquetK0 h₁ hU₁ hfl₁.2.2.1 hfl₁.2.2.2)) =
      (inductionK0 h₀ hU₀ hfl₀.1 hfl₀.2.1).comp
        (jacquetK0 h₀ hU₀ hfl₀.2.2.1 hfl₀.2.2.2) := by
  let _ := hM.locallyCompactSpace
  let R₁ := jacquetFunctor.{uG, max uG uV} h₁ hU₁
  let R₂ := jacquetFunctor.{uG, max uG uV} hL (hU₀.preimage continuous_subtype_val)
  let I₂ := normalizedInductionFunctor.{uG, max uG uV}
    hL (hU₀.preimage continuous_subtype_val)
  let I₁ := normalizedInductionFunctor.{uG, max uG uV} h₁ hU₁
  let R₀ := jacquetFunctor.{uG, max uG uV} h₀ hU₀
  let I₀ := normalizedInductionFunctor.{uG, max uG uV} h₀ hU₀
  have hlII : PreservesFiniteLength (I₂ ⋙ I₁) := hflL.1.comp hfl₁.1
  have hxII : PreservesFiniteLengthShortExact (I₂ ⋙ I₁) :=
    PreservesFiniteLengthShortExact.comp hflL.1 hflL.2.1 hfl₁.2.1
  have hlRII : PreservesFiniteLength (R₂ ⋙ I₂ ⋙ I₁) := hflL.2.2.1.comp hlII
  have hxRII : PreservesFiniteLengthShortExact (R₂ ⋙ I₂ ⋙ I₁) :=
    PreservesFiniteLengthShortExact.comp hflL.2.2.1 hflL.2.2.2 hxII
  have hlAll : PreservesFiniteLength (R₁ ⋙ R₂ ⋙ I₂ ⋙ I₁) := hfl₁.2.2.1.comp hlRII
  have hxAll : PreservesFiniteLengthShortExact (R₁ ⋙ R₂ ⋙ I₂ ⋙ I₁) :=
    PreservesFiniteLengthShortExact.comp hfl₁.2.2.1 hfl₁.2.2.2 hxRII
  have hlRI : PreservesFiniteLength (R₀ ⋙ I₀) := hfl₀.2.2.1.comp hfl₀.1
  have hxRI : PreservesFiniteLengthShortExact (R₀ ⋙ I₀) :=
    PreservesFiniteLengthShortExact.comp hfl₀.2.2.1 hfl₀.2.2.2 hfl₀.2.1
  have hEq := FiniteLengthGrothendieckGroup.map_eq_of_iso
    (inductionJacquetStagesIso h₀ h₁ hM hMM hL hU₀ hU₁ hiStages hrStages)
    hlAll hxAll hlRI hxRI
  change FiniteLengthGrothendieckGroup.map (R₁ ⋙ R₂ ⋙ I₂ ⋙ I₁) hlAll hxAll =
    FiniteLengthGrothendieckGroup.map (R₀ ⋙ I₀) hlRI hxRI at hEq
  rw [FiniteLengthGrothendieckGroup.map_comp R₁ (R₂ ⋙ I₂ ⋙ I₁)
    hfl₁.2.2.1 hfl₁.2.2.2 hlRII hxRII hlAll hxAll,
    FiniteLengthGrothendieckGroup.map_comp R₂ (I₂ ⋙ I₁)
      hflL.2.2.1 hflL.2.2.2 hlII hxII hlRII hxRII,
    FiniteLengthGrothendieckGroup.map_comp I₂ I₁
      hflL.1 hflL.2.1 hfl₁.1 hfl₁.2.1 hlII hxII,
    FiniteLengthGrothendieckGroup.map_comp R₀ I₀
      hfl₀.2.2.1 hfl₀.2.2.2 hfl₀.1 hfl₀.2.1 hlRI hxRI] at hEq
  simpa only [inductionK0, jacquetK0, LinearMap.comp_assoc] using hEq

end Langlands.Aubert.General
