import Langlands.Representation.Exponents.RepresentedParabolicRemarksStatements
import Langlands.Representation.Exponents.LeviUnnormalizedParabolicProof
import Langlands.Representation.Jacquet.SmallFixedVectorGenerator
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # A right adjoint for actual unnormalized parabolic induction -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

namespace SmoothRep

/-- The published direct sums and abelian coequalizers give all small colimits. -/
private theorem hasColimits_commonUniverse (H : Type u) [Group H]
    [TopologicalSpace H] :
    HasColimitsOfSize.{max u v, max u v} (SmoothRep.{0, u, max u v} ℂ H) := by
  classical
  have : HasCoproducts.{max u v} (SmoothRep.{0, u, max u v} ℂ H) := by
    intro I
    refine ⟨fun A => ?_⟩
    have : HasColimit (Discrete.functor (A.obj ∘ Discrete.mk)) :=
      ⟨⟨directSumCofan (A.obj ∘ Discrete.mk),
        directSumIsColimit (A.obj ∘ Discrete.mk)⟩⟩
    exact hasColimit_of_iso (Discrete.natIsoFunctor (F := A))
  exact has_colimits_of_hasCoequalizers_and_coproducts

/-- Open-subgroup permutation modules detect equality on every smooth vector. -/
private theorem openPermutation_isSeparating (H : Type u) [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] :
    (ObjectProperty.ofObj
      (fun K : OpenSubgroup H => Jacquet.smallFixedVectorGenerator.{u, max u v} K)).IsSeparating := by
  intro A B f g hfg
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext x
  change hom f x = hom g x
  obtain ⟨K, hx⟩ := A.isSmooth x
  let t : Jacquet.smallFixedVectorGenerator.{u, max u v} K ⟶ A :=
    ofHom (Jacquet.smallFixedVectorLift K A.representation ⟨x, hx⟩)
  have ht := hfg (Jacquet.smallFixedVectorGenerator K) ⟨K⟩ t
  have he := congrArg (fun a => hom a (Jacquet.smallFixedVectorUnit K)) ht
  change hom f (Jacquet.smallFixedVectorLift K A.representation ⟨x, hx⟩
      (Jacquet.smallFixedVectorUnit K)) =
    hom g (Jacquet.smallFixedVectorLift K A.representation ⟨x, hx⟩
      (Jacquet.smallFixedVectorUnit K)) at he
  simpa only [Jacquet.smallFixedVectorLift_unit] using he

end SmoothRep

namespace Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.1 Remark: actual unnormalized parabolic induction has a right adjoint. -/
theorem leviUnnormalizedInductionRightAdjoint :
    LeviUnnormalizedInductionRightAdjointStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let Ind : SmoothRep.{0, u, max u v} ℂ (rationalPoints M) ⥤
      SmoothRep.{0, u, max u v} ℂ (rationalPoints G) :=
    SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙ inflationFunctor h ⋙
      Induction.smoothInductionFunctor (pointImage p)
  have : PreservesColimitsOfSize.{max u v, max u v} Ind :=
    (leviUnnormalizedFunctorsPreserveLimits.{u, max u v}
      k G hG P M U p l r hp hl hr hmul).2.2
  have := SmoothRep.hasColimits_commonUniverse.{u, v} (rationalPoints M)
  have hsep := SmoothRep.openPermutation_isSeparating.{u, v} (rationalPoints M)
  have : WellPowered.{max u v} (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) :=
    wellPowered_of_isDetecting hsep.isDetecting
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating hsep Ind

end Aubert.General.RepresentedParabolic

end Langlands
