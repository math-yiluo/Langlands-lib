import Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityStatement
import Langlands.AllField.Representation.Whittaker.TwoBlockOpenCell
/-!
# Stability of the two-block cell submodule under the upper unipotent group

Statement of a step in the proof of JPSS Proposition 9.1, printed 453: right
translation by every actual upper unipotent matrix of `GL_(A+B)` maps the cell
submodule `D` of the ordered two-block induction into itself. This is a
proposition definition, not a proof.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier hasCompactSupport_twoBlockCellRestriction twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

universe uF uV

/-- For arbitrary `π₁` and `π₂`, right translation `ξ(u)` by every upper
unipotent `u` of `GL_(A+B)` maps every element of the cell submodule `D` back
into `D`. -/
def TwoBlockCellUnipotentStabilityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂)
    (u : GeneralLinear.upperUnipotent (a + 1 + (b + 1)) F)
    (f : TwoBlockInducedCarrier F a b π₁ π₂),
    f ∈ twoBlockCellSubmodule F a b π₁ π₂ →
      twoBlockInduced F a b π₁ π₂ u.val f ∈ twoBlockCellSubmodule F a b π₁ π₂

end Langlands.AllField.Whittaker
