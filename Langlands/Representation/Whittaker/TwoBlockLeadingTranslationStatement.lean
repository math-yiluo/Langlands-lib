import Langlands.Representation.Whittaker.TwoBlockOpenCell
import Langlands.Representation.Shahidi.TwoBlocks

/-! # Leading-block translation on the actual two-block cell submodule -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear

universe uF uV

/-- Right translation by the leading exchanged block preserves the cell
submodule. Its restriction is the actual inducing action on `x ↦ g⁻¹ x`. -/
def TwoBlockLeadingTranslationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂),
    let T := F.canonicalTopologicalData
    letI := T.topology
    ∀ (g : Langlands.GeneralLinear (b + 1) F.Carrier)
      (f : twoBlockCellSubmodule F a b π₁ π₂),
      let s := Shahidi.swapRank (a + 1) (b + 1) F.Carrier (blockSum (g, 1))
      let m := (Shahidi.twoBlockLeviEquiv
        (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier).symm (1, g)
      twoBlockInduced F a b π₁ π₂ s f.val ∈ twoBlockCellSubmodule F a b π₁ π₂ ∧
        ∀ x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier,
          twoBlockRestriction F a b π₁ π₂
              (twoBlockInduced F a b π₁ π₂ s f.val) x =
            ((T.leviHalfModulus (twoBlockShape a b) m : ℂˣ) : ℂ) •
              (twoBlockShape a b).blockTensor (Shahidi.pairFamily π₁ π₂) m
                (twoBlockCellRestriction F a b π₁ π₂ f (g⁻¹.val * x))

end Langlands.Whittaker
