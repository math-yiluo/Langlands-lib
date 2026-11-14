import Langlands.Representation.Whittaker.TwoBlockCellSectionStatement
import Langlands.AllField.Representation.Whittaker.TwoBlockOpenCell
/-!
# Sections of the two-block cell with prescribed restriction

Statement of the section-existence step in the proof of JPSS Proposition 9.1,
printed 453: for smooth `π₁`, `π₂`, every Schwartz–Bruhat function `Ψ` of
`x` and every tensor `v` are realized as `x ↦ f(w n(x))` for an element `f`
of the cell submodule `D`. This is a proposition definition, not a proof.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellSectionStatement TwoBlockInducedCarrier hasCompactSupport_twoBlockCellRestriction twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

open Langlands.HarmonicAnalysis

universe uF uV

/-- For smooth `π₁` and `π₂`, every Schwartz–Bruhat `Ψ` on `B × A` matrices
and every vector `v` of `V₁ ⊗ V₂` give an induced function `f` in the cell
submodule `D` whose restriction `x ↦ f(w n(x))` is exactly `x ↦ Ψ(x) v`. -/
def TwoBlockCellSectionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂),
    (IsSmooth π₁) →
    (IsSmooth π₂) →
    ∀ (Ψ : SchwartzBruhat (Matrix (Fin (b + 1)) (Fin (a + 1)) F))
      (v : PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)),
      ∃ f : TwoBlockInducedCarrier F a b π₁ π₂,
        f ∈ twoBlockCellSubmodule F a b π₁ π₂ ∧
          ∀ x : Matrix (Fin (b + 1)) (Fin (a + 1)) F,
            twoBlockRestriction F a b π₁ π₂ f x = Ψ x • v

end Langlands.AllField.Whittaker
