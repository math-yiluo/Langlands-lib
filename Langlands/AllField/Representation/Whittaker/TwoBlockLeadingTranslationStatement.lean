import Langlands.Representation.Whittaker.TwoBlockLeadingTranslationStatement
import Langlands.AllField.Representation.Whittaker.TwoBlockOpenCell
/-! # Leading-block translation on the actual two-block cell submodule -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockInducedCarrier TwoBlockLeadingTranslationStatement hasCompactSupport_twoBlockCellRestriction twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear

universe uF uV

/-- Right translation by the leading exchanged block preserves the cell
submodule. Its restriction is the actual inducing action on `x ↦ g⁻¹ x`. -/
def TwoBlockLeadingTranslationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂),
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    ∀ (g : Langlands.GeneralLinear (b + 1) F)
      (f : twoBlockCellSubmodule F a b π₁ π₂),
      let s := Shahidi.swapRank (a + 1) (b + 1) F (blockSum (g, 1))
      let m := (Shahidi.twoBlockLeviEquiv
        (Nat.succ_pos a) (Nat.succ_pos b) F).symm (1, g)
      twoBlockInduced F a b π₁ π₂ s f.val ∈ twoBlockCellSubmodule F a b π₁ π₂ ∧
        ∀ x : Matrix (Fin (b + 1)) (Fin (a + 1)) F,
          twoBlockRestriction F a b π₁ π₂
              (twoBlockInduced F a b π₁ π₂ s f.val) x =
            ((T.leviHalfModulus (twoBlockShape a b) m : ℂˣ) : ℂ) •
              (twoBlockShape a b).blockTensor (Shahidi.pairFamily π₁ π₂) m
                (twoBlockCellRestriction F a b π₁ π₂ f (g⁻¹.val * x))

end Langlands.AllField.Whittaker
