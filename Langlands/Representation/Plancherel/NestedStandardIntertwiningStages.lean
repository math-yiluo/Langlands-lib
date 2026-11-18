import Langlands.Representation.Plancherel.NestedStandardIntertwiningIntegral
import Langlands.Representation.Aubert.General.NestedInductionStages
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Aubert.General.StandardLeviJacquetFiniteLength

/-! # The normalized stages restriction on the actual standard source models -/

noncomputable section

open CategoryTheory Langlands.Aubert.General Langlands.Induction

namespace Langlands.Plancherel.StandardIntertwining

universe u uV

variable {G : Type u} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U Q L N : Subgroup G}
  [LocallyCompactSpace L]
  (h : IsSemidirectDecomposition P M U) (hQ : IsSemidirectDecomposition Q L N)
  (hLc : IsClosed (L : Set G)) (hML : M ≤ L)
  (hL : IsSemidirectDecomposition (P.subgroupOf L) (M.subgroupOf L) (U.subgroupOf L))
  (hU : IsClosed (U : Set G)) (hN : IsClosed (N : Set G))
  (hPQ : P ≤ Q) (hNU : N ≤ U) (hπ : Continuous hQ.projection)
  (hδU : IsUnimodularModulus U hU) (hδN : IsUnimodularModulus N hN)
  (hχ : NestedInduction.HalfCharacterProduct h hQ hLc hL hU hN)
  (A : SmoothRep.{0, u, uV} ℂ M)

local notation "hUi" => hU.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
local notation "Ai" => SmoothRep.pullback (subgroupOfContinuousEquiv hML) A
set_option quotPrecheck false in
local notation "XG" => ↥((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
set_option quotPrecheck false in
local notation "XL" => ↥((DynamicNormalization.leviTwistedInductionFunctor hL hUi).obj Ai)

/-- Evaluate normalized induction in stages on the outer argument `g`,
using the actual Levi-inflated normalization on both source models. -/
def nestedStagesRestriction (hδUi : IsUnimodularModulus (U.subgroupOf L) hUi) (g : G) :
    XG →ₗ[ℂ] XL := by
  let B := (leviNormalizedInductionFunctor hLc hML hL hU).obj A
  let evaluation : ((normalizedInductionFunctor hQ hN).obj B) →ₗ[ℂ] B :=
    { toFun := fun f => eval Q (inducingRepresentation hQ hN B) f g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let source := normalizedInductionLeviEquiv h hU hδU A
  let stages := NestedInduction.equiv h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hχ A
  let inner := normalizedInductionLeviEquiv hL hUi hδUi Ai
  exact inner.toLinearEquiv.toLinearMap.comp
    (evaluation.comp (stages.toLinearEquiv.toLinearMap.comp source.symm.toLinearEquiv.toLinearMap))

/-- The stages restriction removes exactly the outer Levi half-character. -/
theorem nestedStagesRestriction_formula
    (hδUi : IsUnimodularModulus (U.subgroupOf L) hUi) (f : XG) (g : G) :
    NestedRestrictionFormula h hU hL hML A
      (HaarModulus.closedHalfCharacter N hN L hQ.levi_le_normalizer) f g
      (nestedStagesRestriction h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hχ A hδUi g f) := by
  intro l
  exact NestedInduction.equiv_eval h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hχ A
    ((normalizedInductionLeviEquiv h hU hδU A).symm f) g l

/-- Evaluation at the identity is surjective on the actual stages restriction. -/
theorem nestedStagesRestriction_surjective
    (hδUi : IsUnimodularModulus (U.subgroupOf L) hUi) :
    Function.Surjective
      (nestedStagesRestriction h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hχ A hδUi 1) := by
  intro f
  let B := (leviNormalizedInductionFunctor hLc hML hL hU).obj A
  let source := normalizedInductionLeviEquiv h hU hδU A
  let stages := NestedInduction.equiv h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hχ A
  let inner := normalizedInductionLeviEquiv hL hUi hδUi Ai
  obtain ⟨F, hF⟩ := normalizedInduction_eval_surjective hQ hN hπ B (inner.symm f)
  refine ⟨source (stages.symm F), ?_⟩
  change inner.toLinearEquiv (eval Q (inducingRepresentation hQ hN B)
    (stages.toLinearEquiv (source.toLinearEquiv.symm
      (source.toLinearEquiv (stages.toLinearEquiv.symm F)))) 1) = f
  rw [LinearEquiv.symm_apply_apply]
  have hEval := congrArg (fun f => eval Q (inducingRepresentation hQ hN B) f 1)
    (stages.toLinearEquiv.apply_symm_apply F)
  exact (congrArg inner.toLinearEquiv (hEval.trans hF)).trans
    (inner.toLinearEquiv.apply_symm_apply f)

omit [LocallyCompactSpace L] in
/-- Compact subgroup containment makes the outer Levi half-character trivial
on the inner target radical. -/
theorem outerHalfCharacter_one_on_innerTargetRadical {U' : Subgroup G}
    (hU'Q : U' ≤ Q) (hU'c : Jacquet.Localization.IsLimitOfCompactSubgroups U')
    (u : U'.subgroupOf L) :
    HaarModulus.closedHalfCharacter N hN L hQ.levi_le_normalizer u.val = 1 :=
  closedHalfCharacter_eq_one_of_isLimitOfCompactSubgroups hQ hN hU'Q hU'c
    (nestedTargetRadicalSection u)

end Langlands.Plancherel.StandardIntertwining
