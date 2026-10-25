import Langlands.Representation.Induction.OppositeProductReversalStatement
import Langlands.Representation.Induction.ConjugateParabolic
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Tensor.FiniteRegrouping

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.GeneralLinear.BlockShape

universe uF
variable {n : ℕ} (B : BlockShape n) (F : Type uF) [CommRing F]

/-- Conjugation by the block reversal, from reversed upper to original lower. -/
def reverseToOpposite : B.reverse.parabolic F ≃* B.oppositeParabolic F where
  toFun q := ⟨MulAut.conj (B.reverseMatrix F) q,
    (B.reverseMatrix_conj_mem_oppositeParabolic_iff F q).mpr q.property⟩
  invFun p := ⟨(MulAut.conj (B.reverseMatrix F)).symm p, by
    apply (B.reverseMatrix_conj_mem_oppositeParabolic_iff F _).mp
    simpa only [MulEquiv.apply_symm_apply] using p.property⟩
  left_inv q := Subtype.ext ((MulAut.conj (B.reverseMatrix F)).symm_apply_apply q)
  right_inv p := Subtype.ext ((MulAut.conj (B.reverseMatrix F)).apply_symm_apply p)
  map_mul' q r := Subtype.ext ((MulAut.conj (B.reverseMatrix F)).map_mul q r)

@[simp] theorem reverseToOpposite_apply (q : B.reverse.parabolic F) :
    (B.reverseToOpposite F q : GeneralLinear n F) =
      B.reverseMatrix F * q * (B.reverseMatrix F)⁻¹ := rfl

/-- The actual lower projection has precisely the reversed diagonal blocks. -/
theorem oppositeLeviProjection_reverseToOpposite (q : B.reverse.parabolic F)
    (i : Fin B.length) :
    B.oppositeLeviProjection F (B.reverseToOpposite F q) i.rev =
      B.reverse.leviProjection F q i := by
  apply Units.ext
  ext a b
  exact B.reverseMatrix_conjugate_entry F q i i a b

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

universe uF
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Reversing the ordered pairs in the explicit determinant product inverts it. -/
theorem leviModulus_reverse (m : B.Levi F.Carrier) :
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
theorem leviHalfModulus_reverse (m : B.Levi F.Carrier) :
    T.leviHalfModulus B.reverse (fun i => m i.rev) =
      (T.leviHalfModulus B m)⁻¹ := by
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    ((Units.map NNReal.sqrtHom.toMonoidHom)
      (T.leviModulus B.reverse (fun i => m i.rev))) = _
  rw [T.leviModulus_reverse B m, map_inv, map_inv]
  rfl

/-- The two normalizations agree on conjugate parabolic elements. -/
theorem oppositeHalfModulus_reverseToOpposite (q : B.reverse.parabolic F.Carrier) :
    T.oppositeParabolicHalfModulus B (B.reverseToOpposite F.Carrier q) =
      T.parabolicHalfModulus B.reverse q := by
  rw [oppositeParabolicHalfModulus_apply, parabolicHalfModulus_apply,
    ← leviHalfModulus_reverse]
  congr 1
  funext i
  exact B.oppositeLeviProjection_reverseToOpposite F.Carrier q i

end Langlands.PadicField.TopologicalData

namespace Langlands

universe uF uV

/-- The canonical reversal comparison, with both prescribed evaluation laws. -/
theorem glOppositeProductReversal : GLOppositeProductReversalStatement.{uF,uV} := by
  intro p hp F T
  let := T.topology
  intro n B
  let := T.generalLinearTopologicalGroup n
  intro V hadd hmod σ _hσ
  let : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
  let w := B.reverseMatrix F.Carrier
  let R : PiTensorProduct ℂ V ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i : Fin B.reverse.length => V i.rev) :=
    PiTensorProduct.reindex ℂ V Fin.revPerm
  let e := B.reverseToOpposite F.Carrier
  let ρ := twist (T.oppositeParabolicHalfModulus B)
    ((B.blockTensor σ).comp (B.oppositeLeviProjection F.Carrier))
  let α : Representation ℂ (B.reverse.parabolic F.Carrier) (PiTensorProduct ℂ V) :=
    ρ.comp e.toMonoidHom
  let τ := twist (T.parabolicHalfModulus B.reverse)
    ((B.reverse.blockTensor (V := fun i => V i.rev) (fun i => σ i.rev)).comp
      (B.reverse.leviProjection F.Carrier))
  have hm (q : B.reverse.parabolic F.Carrier) :
      B.oppositeLeviProjection F.Carrier (e q) =
        (FiniteTensor.reindexGroup
          (fun i => GeneralLinear (B.size i) F.Carrier) Fin.revPerm).symm
          (B.reverse.leviProjection F.Carrier q) := by
    apply (FiniteTensor.reindexGroup
      (fun i => GeneralLinear (B.size i) F.Carrier) Fin.revPerm).injective
    erw [MulEquiv.apply_symm_apply]
    funext i
    exact B.oppositeLeviProjection_reverseToOpposite F.Carrier q i
  let D : α.Equiv τ := Representation.Equiv.mk R (fun q => by
    apply LinearMap.ext
    intro v
    change R ((T.oppositeParabolicHalfModulus B (e q) : ℂ) •
      B.blockTensor σ (B.oppositeLeviProjection F.Carrier (e q)) v) =
      (T.parabolicHalfModulus B.reverse q : ℂ) •
        B.reverse.blockTensor (fun i => σ i.rev) (B.reverse.leviProjection F.Carrier q) (R v)
    rw [map_smul, T.oppositeHalfModulus_reverseToOpposite B q]
    congr 1
    rw [hm q]
    exact FiniteTensor.reindexEquiv_apply_action Fin.revPerm σ
      (B.reverse.leviProjection F.Carrier q) v)
  let C : (Induction.smoothInduced _ α).Equiv (Induction.smoothInduced _ ρ) :=
    Induction.conjugateSmoothInducedEquiv w e (fun _ => rfl) (fun _ => rfl)
  refine ⟨C.symm.trans (Induction.smoothInducedEquiv _ D), ?_, ?_⟩
  · intro f x
    rfl
  · intro h x
    rfl

end Langlands
