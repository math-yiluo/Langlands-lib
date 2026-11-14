import Langlands.Representation.Induction.OppositeProductReversalProof
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Representation.Induction.Equivalences
import Langlands.AllField.Representation.Induction.OppositeProductReversalStatement
noncomputable section

open scoped BigOperators NNReal

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape hiding HasBlockIwahoriFactorization IsWeaklyContracting
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF

end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF
variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Reversing the ordered pairs in the explicit determinant product inverts it. -/
theorem leviModulus_reverse (m : B.Levi F) :
    T.leviModulus B.reverse (fun i => m i.rev) = (T.leviModulus B m)⁻¹ := by
  classical
  erw [T.leviModulus_apply B.reverse, T.leviModulus_apply B]
  simp only [Finset.prod_filter]
  change (∏ i : Fin B.length, ∏ j : Fin B.length,
      if i < j then T.determinantNorm (B.size i.rev) (m i.rev) ^ B.size j.rev /
        T.determinantNorm (B.size j.rev) (m j.rev) ^ B.size i.rev else 1) = _
  calc
    _ = ∏ i : Fin B.length, ∏ j : Fin B.length,
        if j < i then T.determinantNorm (B.size i) (m i) ^ B.size j /
          T.determinantNorm (B.size j) (m j) ^ B.size i else 1 := by
      apply Fintype.prod_equiv Fin.revPerm _ _
      intro i
      apply Fintype.prod_equiv Fin.revPerm _ _
      intro j
      simp only [Fin.revPerm_apply, Fin.rev_lt_rev]
      rfl
    _ = ∏ j : Fin B.length, ∏ i : Fin B.length,
        if j < i then T.determinantNorm (B.size i) (m i) ^ B.size j /
          T.determinantNorm (B.size j) (m j) ^ B.size i else 1 := Finset.prod_comm
    _ = _ := by
      simp only [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      split_ifs <;> simp

/-- The canonical positive square root respects inversion. -/
theorem leviHalfModulus_reverse (m : B.Levi F) :
    T.leviHalfModulus B.reverse (fun i => m i.rev) =
      (T.leviHalfModulus B m)⁻¹ := by
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    ((Units.map NNReal.sqrtHom.toMonoidHom)
      (T.leviModulus B.reverse (fun i => m i.rev))) = _
  rw [T.leviModulus_reverse B m, map_inv, map_inv]
  rfl

/-- The two normalizations agree on conjugate parabolic elements. -/
theorem oppositeHalfModulus_reverseToOpposite (q : B.reverse.parabolic F) :
    T.oppositeParabolicHalfModulus B (B.reverseToOpposite F q) =
      T.parabolicHalfModulus B.reverse q := by
  rw [oppositeParabolicHalfModulus_apply, parabolicHalfModulus_apply,
    ← leviHalfModulus_reverse]
  congr 1
  funext i
  exact B.oppositeLeviProjection_reverseToOpposite F q i

end Langlands.LocalFieldData

namespace Langlands.AllField

universe uF uV

/-- The canonical reversal comparison, with both prescribed evaluation laws. -/
theorem glOppositeProductReversal : GLOppositeProductReversalStatement.{uF,uV} := by
  intro F _ T
  let := T.topology
  intro n B
  let := T.generalLinearTopologicalGroup n
  intro V hadd hmod σ _hσ
  let : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
  let w := B.reverseMatrix F
  let R : PiTensorProduct ℂ V ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i : Fin B.reverse.length => V i.rev) :=
    PiTensorProduct.reindex ℂ V Fin.revPerm
  let e := B.reverseToOpposite F
  let ρ := twist (T.oppositeParabolicHalfModulus B)
    ((B.blockTensor σ).comp (B.oppositeLeviProjection F))
  let α : Representation ℂ (B.reverse.parabolic F) (PiTensorProduct ℂ V) :=
    ρ.comp e.toMonoidHom
  let τ := twist (T.parabolicHalfModulus B.reverse)
    ((B.reverse.blockTensor (V := fun i => V i.rev) (fun i => σ i.rev)).comp
      (B.reverse.leviProjection F))
  have hm (q : B.reverse.parabolic F) :
      B.oppositeLeviProjection F (e q) =
        (FiniteTensor.reindexGroup
          (fun i => GeneralLinear (B.size i) F) Fin.revPerm).symm
          (B.reverse.leviProjection F q) := by
    apply (FiniteTensor.reindexGroup
      (fun i => GeneralLinear (B.size i) F) Fin.revPerm).injective
    erw [MulEquiv.apply_symm_apply]
    funext i
    exact B.oppositeLeviProjection_reverseToOpposite F q i
  let D : α.Equiv τ := Representation.Equiv.mk R (fun q => by
    apply LinearMap.ext
    intro v
    change R ((T.oppositeParabolicHalfModulus B (e q) : ℂ) •
      B.blockTensor σ (B.oppositeLeviProjection F (e q)) v) =
      (T.parabolicHalfModulus B.reverse q : ℂ) •
        B.reverse.blockTensor (fun i => σ i.rev) (B.reverse.leviProjection F q) (R v)
    rw [map_smul, T.oppositeHalfModulus_reverseToOpposite B q]
    congr 1
    rw [hm q]
    exact FiniteTensor.reindexEquiv_apply_action Fin.revPerm σ
      (B.reverse.leviProjection F q) v)
  let C : (Induction.smoothInduced _ α).Equiv (Induction.smoothInduced _ ρ) :=
    Induction.conjugateSmoothInducedEquiv w e (fun _ => rfl) (fun _ => rfl)
  refine ⟨C.symm.trans (Induction.smoothInducedEquiv _ D), ?_, ?_⟩
  · intro f x
    rfl
  · intro h x
    rfl

end Langlands.AllField
