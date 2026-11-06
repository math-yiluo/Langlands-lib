import Langlands.Representation.Aubert.General.FirstAdjointness
import Langlands.Representation.Category.SmoothUniverseLiftLimits
import Langlands.Representation.Induction.Equivalences

/-! # Small limit preservation under normalized induction

Carrier-saturated first adjointness and carrier-lift preservation transfer
limit preservation to the original explicit small diagram size.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false

universe uG uV

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))

/-- The published cross-universe reciprocity gives a categorical adjunction
when the carriers are saturated to contain the group universe. -/
def firstAdjointnessAdjunction (hδ : IsUnimodularModulus U hU) :
    jacquetFunctor.{uG, max uG uV} h hU ⊣
      normalizedInductionFunctor.{uG, max uG uV} h hU :=
  Adjunction.mkOfHomEquiv
    { homEquiv A B :=
        { toFun f := SmoothRep.ofHom
            ((FirstAdjointness.equiv h hU hδ A B).symm (SmoothRep.hom f))
          invFun f := SmoothRep.ofHom
            (FirstAdjointness.equiv h hU hδ A B (SmoothRep.hom f))
          left_inv f := by
            change SmoothRep.ofHom
              ((FirstAdjointness.equiv h hU hδ A B)
                ((FirstAdjointness.equiv h hU hδ A B).symm (SmoothRep.hom f))) = f
            rw [LinearEquiv.apply_symm_apply, SmoothRep.ofHom_hom]
          right_inv f := by
            change SmoothRep.ofHom
              ((FirstAdjointness.equiv h hU hδ A B).symm
                ((FirstAdjointness.equiv h hU hδ A B) (SmoothRep.hom f))) = f
            rw [LinearEquiv.symm_apply_apply, SmoothRep.ofHom_hom] }
      homEquiv_naturality_left_symm f g := by
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply Jacquet.Localization.hom_ext
        ext v
        rfl
      homEquiv_naturality_right f g := by
        apply ObjectProperty.hom_ext
        ext v
        rfl }

/-- Raising an inducing carrier changes its induced functions by postcomposition
with `down`, so the original and saturated inductions are naturally isomorphic. -/
def normalizedInductionUniverseLiftIso :
    SmoothRep.universeLiftFunctor.{uG, uG, uV} M ⋙
        normalizedInductionFunctor.{uG, max uG uV} h hU ≅
      normalizedInductionFunctor.{uG, uV} h hU :=
  NatIso.ofComponents (fun A => SmoothRep.mkIso
    (Induction.smoothInducedEquiv P
      (Representation.Equiv.mk (ULift.moduleEquiv (R := ℂ) (M := A)) (fun p => by
        ext v
        rfl)))) (by
    intro A B f
    apply ObjectProperty.hom_ext
    ext v
    rfl)

/-- Normalized induction preserves limits at the original carrier size,
provided the radical has trivial inner Haar modulus. -/
theorem normalizedInductionFunctor_preservesLimits (hδ : IsUnimodularModulus U hU) :
    PreservesLimitsOfSize.{uV, uV} (normalizedInductionFunctor.{uG, uV} h hU) := by
  have : PreservesLimitsOfSize.{max uG uV, max uG uV}
      (normalizedInductionFunctor.{uG, max uG uV} h hU) :=
    (firstAdjointnessAdjunction h hU hδ).rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{uV, uV}
      (normalizedInductionFunctor.{uG, max uG uV} h hU) :=
    preservesLimitsOfSize_shrink.{uV, uG, uV, uG} _
  exact preservesLimits_of_natIso (normalizedInductionUniverseLiftIso h hU)

end Langlands.Aubert.General
