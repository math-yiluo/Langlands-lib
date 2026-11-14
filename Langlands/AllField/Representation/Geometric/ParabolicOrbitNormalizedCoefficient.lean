import Langlands.Representation.Geometric.ParabolicOrbitNormalizedCoefficient
import Langlands.AllField.Representation.Geometric.ParabolicOrbitNormalization
/-! The actual normalized orbit coefficient is the refined induction coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem refinedLeviModulus_of_diagonal
open Langlands.AllField.Geometric

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
universe uF uV uW


end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem refinedLeviModulus_of_diagonal
open Langlands.AllField.Geometric
universe uF uV uW

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)
  (w : MinimalRepresentatives B C) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F) B C w.val S)
  (hR : IsIntersectionRefinement (F := F) C B w.val⁻¹ R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual coefficient after quotient integration and target normalization. -/
abbrev parabolicOrbitNormalizedNestedCoefficient
    (ρ : Representation ℂ (B.Levi F) V) :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.fieldT2
  letI := T.generalLinearLocallyCompactSpace n
  twist ((Jacquet.inverseHalfCharacter (T.leviModulus C)).comp
      (parabolicOrbitStagesQuotient F B C w.val).subtype)
    (twist (Jacquet.complexCharacter (parabolicOrbitStagesHaarRatio F B C w.val))
      (parabolicOrbitNestedCoefficientAction F B C w.val (T.leviHalfModulus B) ρ))

/-- The normalized nested coefficient is exactly the pulled-back refined induction
coefficient, with no residual character. -/
def parabolicOrbitNormalizedNestedCoefficientEquiv
    (ρ : Representation ℂ (B.Levi F) V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    (T.parabolicOrbitNormalizedNestedCoefficient B C w ρ).Equiv
      ((twist (T.refinedParabolicHalfModulus C R)
        ((refinedIntersectionTransport F B C w.val S R hS.2.1 hR.2.1
          (T.normalizedRefinedJacquet B S ρ)).comp
            (refinedLeviProjection F C R))).comp
              (parabolicOrbitStagesRefinedEquiv F B C w.val R hR).toMonoidHom) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let e := T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w.val S R hS hR ρ
  refine { toLinearEquiv := e.toLinearEquiv, isIntertwining' := ?_ }
  intro l
  apply LinearMap.ext
  intro z
  change e ((Jacquet.inverseHalfCharacter (T.leviModulus C) l.val : ℂ) •
      ((Jacquet.complexCharacter (parabolicOrbitStagesHaarRatio F B C w.val) l : ℂ) •
        parabolicOrbitNestedCoefficientAction F B C w.val (T.leviHalfModulus B) ρ l z)) =
    (T.refinedParabolicHalfModulus C R
      (parabolicOrbitStagesRefinedEquiv F B C w.val R hR l) : ℂ) •
        T.normalizedRefinedJacquet B S ρ
          (parabolicOrbitSourceRefinedCoordinate F B C w.val R hR S hS l) (e z)
  rw [map_smul, map_smul]
  have he := congrArg (fun f => f z) (e.isIntertwining' l)
  change e (parabolicOrbitNestedCoefficientAction F B C w.val
      (T.leviHalfModulus B) ρ l z) =
    (T.parabolicOrbitSectionCharacter B C w.val S R hS hR l : ℂ) •
      T.normalizedRefinedJacquet B S ρ
        (parabolicOrbitSourceRefinedCoordinate F B C w.val R hR S hS l) (e z) at he
  rw [he, smul_smul, smul_smul]
  have hc := congrArg (fun a : ℂˣ => (a : ℂ))
    (T.parabolicOrbitNormalization_cancel B C w S R hS hR l)
  simp only [Units.val_mul] at hc
  rw [hc]

/-- This coefficient equivalence commutes with every source intertwiner. -/
theorem parabolicOrbitNormalizedNestedCoefficientEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W} (f : ρ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ z : Representation.Coinvariants
      (parabolicOrbitNestedCoefficient F B C w.val (T.leviHalfModulus B) ρ),
    T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR τ
      (Representation.Coinvariants.map _ _
        (parabolicOrbitNestedCoefficientMap F B C w.val (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact T.parabolicOrbitNestedRefinedCoefficientActionEquiv_natural B C w.val S R hS hR f

end Langlands.LocalFieldData
