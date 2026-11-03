import Langlands.Representation.Aubert.General.AlternatingOperator

/-! # Induction stages on exact finite-length K0 -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
  (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
  (hM : IsClosed (M₁ : Set G)) (hMM : M₀ ≤ M₁)
  (hL : IsSemidirectDecomposition
    (P₀.subgroupOf M₁) (M₀.subgroupOf M₁) (U₀.subgroupOf M₁))
  (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))
  (hflL : letI := hM.locallyCompactSpace
    PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV}
      hL (hU₀.preimage continuous_subtype_val)) ∧
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV}
      hL (hU₀.preimage continuous_subtype_val)))

/-- Actual fine-to-coarse induction on exact K0, including the canonical
identification with the fine Levi's literal subgroup copy. -/
def leviInductionK0 :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ M₀ →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ M₁ :=
  letI := hM.locallyCompactSpace
  (inductionK0 hL (hU₀.preimage continuous_subtype_val) hflL.1 hflL.2).comp
    (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hMM))

variable
  (hfl₀ : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h₀ hU₀) ∧
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV} h₀ hU₀))
  (hfl₁ : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h₁ hU₁) ∧
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV} h₁ hU₁))
  (hStages : leviNormalizedInductionFunctor.{uG, max uG uV} hM hMM hL hU₀ ⋙
      normalizedInductionFunctor h₁ hU₁ ≅ normalizedInductionFunctor h₀ hU₀)

include hStages in
/-- A stages isomorphism gives equality on the whole exact finite-length K0. -/
theorem inductionK0_comp_leviInductionK0 :
    (inductionK0 h₁ hU₁ hfl₁.1 hfl₁.2).comp
        (leviInductionK0.{uG, uV} hM hMM hL hU₀ hflL) =
      inductionK0 h₀ hU₀ hfl₀.1 hfl₀.2 := by
  let _ := hM.locallyCompactSpace
  let E := SmoothRep.pullbackFunctor.{uG, uG, max uG uV}
    (subgroupOfContinuousEquiv hMM)
  let IL := normalizedInductionFunctor.{uG, max uG uV}
    hL (hU₀.preimage continuous_subtype_val)
  let I₁ := normalizedInductionFunctor.{uG, max uG uV} h₁ hU₁
  let I₀ := normalizedInductionFunctor.{uG, max uG uV} h₀ hU₀
  have hlE : PreservesFiniteLength E := pullbackFunctor_preservesFiniteLength _
  have hxE : PreservesFiniteLengthShortExact E := pullbackFunctor_preservesShortExact _
  have hlEL : PreservesFiniteLength (E ⋙ IL) := hlE.comp hflL.1
  have hxEL : PreservesFiniteLengthShortExact (E ⋙ IL) :=
    PreservesFiniteLengthShortExact.comp hlE hxE hflL.2
  have hlAll : PreservesFiniteLength ((E ⋙ IL) ⋙ I₁) := hlEL.comp hfl₁.1
  have hxAll : PreservesFiniteLengthShortExact ((E ⋙ IL) ⋙ I₁) :=
    PreservesFiniteLengthShortExact.comp hlEL hxEL hfl₁.2
  have hEq := FiniteLengthGrothendieckGroup.map_eq_of_iso
    hStages hlAll hxAll hfl₀.1 hfl₀.2
  change FiniteLengthGrothendieckGroup.map ((E ⋙ IL) ⋙ I₁) hlAll hxAll =
    FiniteLengthGrothendieckGroup.map I₀ hfl₀.1 hfl₀.2 at hEq
  rw [FiniteLengthGrothendieckGroup.map_comp (E ⋙ IL) I₁
      hlEL hxEL hfl₁.1 hfl₁.2 hlAll hxAll,
    FiniteLengthGrothendieckGroup.map_comp E IL
      hlE hxE hflL.1 hflL.2 hlEL hxEL] at hEq
  exact hEq

include hStages in
/-- The same stages equality with domain the literal fine subgroup inside the
coarse Levi, so that it composes directly with restricted Jacquet maps. -/
theorem inductionK0_comp_restrictedInductionK0 :
    letI := hM.locallyCompactSpace
    (inductionK0 h₁ hU₁ hfl₁.1 hfl₁.2).comp
        (inductionK0 hL (hU₀.preimage continuous_subtype_val) hflL.1 hflL.2) =
      (inductionK0 h₀ hU₀ hfl₀.1 hfl₀.2).comp
        (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hMM).symm) := by
  let _ := hM.locallyCompactSpace
  have hEq := congrArg
    (fun f => f.comp
      (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hMM).symm))
    (inductionK0_comp_leviInductionK0 h₀ h₁ hM hMM hL hU₀ hU₁ hflL
      hfl₀ hfl₁ hStages)
  have hCancel :
      (FiniteLengthGrothendieckGroup.pullback.{uG, uG, max uG uV}
          (subgroupOfContinuousEquiv hMM)).comp
          (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hMM).symm) =
        LinearMap.id :=
    FiniteLengthGrothendieckGroup.pullback_symm_comp
      (subgroupOfContinuousEquiv hMM).symm
  simpa only [leviInductionK0, LinearMap.comp_assoc,
    hCancel, LinearMap.comp_id] using hEq

end Langlands.Aubert.General
