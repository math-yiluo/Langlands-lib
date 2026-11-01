import Langlands.Algebra.NonUnitalModuleFixedBidualStatements

/-! Internal fixed-bidual inverse and evaluation comparison for Renard I.5.1. -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleFixedBidualProof

open MulOpposite NonUnitalModuleDual NonUnitalModuleFixedBidualMaps
open NonUnitalModuleFixedBidualStatements
open NonUnitalModuleCorner (FixedPart)

universe uA uM

/-- The actual comparison maps are mutually inverse and preserve canonical evaluation. -/
theorem fixedBidualComparisons : FixedBidualComparisons.{uA, uM} := by
  intro A _ _ _ _ M _ _ hA hM
  let _ := dualAction hA hM
  let _ := bidualAction hA hM
  let _ := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
  constructor
  · intro e
    let _ := NondegenerateScalars.complexModule hA hM
    let _ := NonUnitalModuleCorner.complexModule hA hM e
    let _ := NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e
    constructor
    · intro Φ
      apply Subtype.ext
      apply Subtype.ext
      apply LinearMap.ext
      intro φ
      change Φ.val.val (extendToDual hA hM e (restrictFromDual hA hM e φ)) =
        Φ.val.val φ
      have h : extendToDual hA hM e (restrictFromDual hA hM e φ) =
          op (e : A) • φ := by
        apply Subtype.ext
        apply LinearMap.ext
        intro m
        rfl
      rw [h]
      exact congrArg (fun Ψ : Bidual hA hM => Ψ.val φ) Φ.property
    · intro Ψ
      apply LinearMap.ext
      intro ell
      change Ψ (restrictFromDual hA hM e (extendToDual hA hM e ell)) = Ψ ell
      apply congrArg Ψ
      apply LinearMap.ext
      intro x
      change ell (NonUnitalModuleCorner.projection e x.val) = ell x
      exact congrArg ell (Subtype.ext x.property)
  · intro e
    let _ := NonUnitalModuleCorner.complexModule hA hM e
    intro x
    apply Subtype.ext
    apply LinearMap.ext
    intro φ
    rfl

example : FixedBidualComparisons.{uA, uM} := fixedBidualComparisons.{uA, uM}
example : FixedBidualComparisons.{0, 1} := fixedBidualComparisons.{0, 1}
example : FixedBidualComparisons.{2, 0} := fixedBidualComparisons.{2, 0}

end Langlands.Algebra.NonUnitalModuleFixedBidualProof
