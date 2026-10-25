import Langlands.Group.GL.ReverseBlocks
import Langlands.Representation.Induction.OppositeParabolic
import Langlands.Representation.Induction.BlockFactors

/-!
# Opposite induction and reversed upper block products

An internal transport statement with both canonical evaluation formulas.
The block reversal preserves coordinates within each block.
-/

namespace Langlands

universe uF uV

/-- Opposite normalized induction of a block tensor is the upper normalized
product of the reversed block family, with the specified function maps. -/
def GLOppositeProductReversalStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      ∀ (V : Fin B.length → Type uV) [hadd : ∀ i, AddCommGroup (V i)]
        [hmod : ∀ i, Module ℂ (V i)]
        (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)),
        (∀ i, IsSmooth (σ i)) →
        letI : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) :=
          fun i => hadd i.rev
        letI : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) :=
          fun i => hmod i.rev
        let w := B.reverseMatrix F.Carrier
        let R : PiTensorProduct ℂ V ≃ₗ[ℂ]
            PiTensorProduct ℂ (fun i : Fin B.reverse.length => V i.rev) :=
          PiTensorProduct.reindex ℂ V Fin.revPerm
        ∃ E : Representation.Equiv
            (T.normalizedOppositeParabolicInduced B (B.blockTensor σ))
            (T.normalizedProductInduced B.reverse (V := fun i => V i.rev)
              (fun i => σ i.rev)),
          (∀ f x, Induction.eval _ _ (E f) x =
            R (Induction.eval _ _ f (w * x))) ∧
          (∀ h x, Induction.eval _ _ (E.symm h) x =
            R.symm (Induction.eval _ _ h (w⁻¹ * x)))

end Langlands
