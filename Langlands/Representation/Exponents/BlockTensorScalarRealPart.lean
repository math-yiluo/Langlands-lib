import Langlands.Representation.Exponents.DescendingIntervalBlockScalarProof
import Langlands.Representation.CuspidalSupport.BlockPermutation
import Langlands.Representation.Exponents.Jacquet

/-! # Scalar real parts on arbitrary actual block tensors -/

noncomputable section

namespace Langlands

open scoped BigOperators

universe uF uV

/-- Original scalar characters and real coordinates survive a permutation of
arbitrary actual smooth block factors. -/
theorem blockTensorScalarRealPart {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
      (Y : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (c : Fin B.length → (F.Carrierˣ →* ℂˣ))
      (x : Fin B.length → ℝ),
      (∀ i, Classification.HasScalarCharacter (Y i).representation
        GeneralLinear.scalar (c i)) →
      (∀ i (a : F.Carrierˣ), ‖(c i a : ℂ)‖ =
        T.normalizedAbs (a : F.Carrier) ^ x i) →
      ∀ e : Equiv.Perm (Fin B.length),
        let χ := ∏ i, (c (e i)).comp
          (Pi.evalMonoidHom (fun _ : Fin B.length => F.Carrierˣ) i)
        Classification.HasScalarCharacter
          ((B.permute e).blockTensor (fun i => (Y (e i)).representation))
          ((B.permute e).blockScalarLevi F.Carrier) χ ∧
        T.IsRealPartOf χ (x ∘ e) := by
  classical
  let := T.topology
  intro n B Y c x hc hx e
  refine ⟨(B.permute e).hasScalarCharacter_blockTensor_splitCentre F.Carrier
    (fun i => hc (e i)), ?_⟩
  intro a
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ => hx (e i) (a i)

end Langlands
