import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Properness reflected along a surjective closed immersion of the base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SurjectiveClosedBaseChange

variable {X S T : Scheme.{u}} (p : X ⟶ S) (t : T ⟶ S)

/-- The comparison from the fibre square of the base change to the fibre square of `p`. -/
abbrev squareMap : pullback (pullback.snd p t) (pullback.snd p t) ⟶ pullback p p :=
  pullback.map _ _ _ _ (pullback.fst p t) (pullback.fst p t) t pullback.condition.symm
    pullback.condition.symm

/-- The fibre square of the base change is the base change of the fibre square. -/
theorem isPullback_squareMap :
    IsPullback (squareMap p t) (pullback.fst _ _ ≫ pullback.snd p t) (pullback.fst p p ≫ p) t := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · simp [pullback.condition]
  · refine pullback.lift (pullback.lift (s.fst ≫ pullback.fst p p) s.snd ?_)
      (pullback.lift (s.fst ≫ pullback.snd p p) s.snd ?_) ?_
    · simpa using s.condition
    · rw [Category.assoc, ← pullback.condition]
      simpa using s.condition
    · simp
  · apply pullback.hom_ext <;> simp
  · simp
  · have h₁' : m ≫ squareMap p t = s.fst := h₁
    apply pullback.hom_ext (f := pullback.snd p t) (g := pullback.snd p t)
    · apply pullback.hom_ext (f := p) (g := t)
      · have := congrArg (· ≫ pullback.fst p p) h₁'
        simpa using this
      · simpa using h₂
    · apply pullback.hom_ext (f := p) (g := t)
      · have := congrArg (· ≫ pullback.snd p p) h₁'
        simpa using this
      · simp only [Category.assoc, pullback.lift_snd]
        rw [← pullback.condition]
        exact h₂

variable [IsClosedImmersion t] [Surjective t]

theorem universallyClosed [UniversallyClosed (pullback.snd p t)] : UniversallyClosed p := by
  have : UniversallyClosed (pullback.fst p t ≫ p) := by
    rw [pullback.condition]
    infer_instance
  have : Surjective (pullback.fst p t) := inferInstance
  exact UniversallyClosed.of_comp_surjective (pullback.fst p t) p

theorem isSeparated [IsSeparated (pullback.snd p t)] : IsSeparated p := by
  have hG : IsClosedImmersion (squareMap p t) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_squareMap p t).flip
      inferInstance
  have hF : Surjective (pullback.fst p t) := inferInstance
  have hcomm : pullback.fst p t ≫ pullback.diagonal p =
      pullback.diagonal (pullback.snd p t) ≫ squareMap p t := by
    apply pullback.hom_ext <;> simp
  have hrange : Set.range (pullback.diagonal p) =
      squareMap p t '' Set.range (pullback.diagonal (pullback.snd p t)) := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, ← hcomm,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hF.surj.range_eq,
      Set.image_univ]
  have hclosed : IsClosed (Set.range (pullback.diagonal p)) := by
    rw [hrange]
    exact (squareMap p t).isClosedEmbedding.isClosedMap _
      (pullback.diagonal (pullback.snd p t)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

theorem isProper [IsProper (pullback.snd p t)] [LocallyOfFiniteType p] : IsProper p := by
  have := isSeparated p t
  have := universallyClosed p t
  constructor

end Langlands.AlgebraicGeometry.SurjectiveClosedBaseChange
