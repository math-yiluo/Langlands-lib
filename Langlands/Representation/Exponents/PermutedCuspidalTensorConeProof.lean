import Langlands.Representation.Exponents.PermutedCuspidalTensorConeStatement
import Langlands.Representation.Exponents.SquareIntegrableActualJacquetConeProof
import Langlands.Representation.Exponents.DescendingIntervalBlockScalarProof
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Keeping original scalar witnesses through actual tensor permutations -/

noncomputable section

namespace Langlands

open scoped BigOperators

universe uF uV

/-- Reuse the original characters and coordinates on a permuted actual tensor. -/
theorem permutedCuspidalTensorScalar {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
      (C : ∀ i, GeneralLinear.SupercuspidalRep.{uF,uV}
        (F := F.Carrier) (n := B.size i))
      (c : Fin B.length → (F.Carrierˣ →* ℂˣ))
      (x : Fin B.length → ℝ),
      (∀ i, Classification.HasScalarCharacter (C i).obj.representation
        GeneralLinear.scalar (c i)) →
      (∀ i (a : F.Carrierˣ), ‖(c i a : ℂ)‖ =
        T.normalizedAbs (a : F.Carrier) ^ (x i)) →
      ∀ e : Equiv.Perm (Fin B.length),
        let χ := ∏ i, (c (e i)).comp
          (Pi.evalMonoidHom (fun _ : Fin B.length => F.Carrierˣ) i)
        Classification.HasScalarCharacter
          ((B.permute e).blockTensor (fun i => (C (e i)).obj.representation))
          ((B.permute e).blockScalarLevi F.Carrier) χ ∧
        T.IsRealPartOf χ (x ∘ e) := by
  classical
  let := T.topology
  intro n B C c x hc hx e
  refine ⟨(B.permute e).hasScalarCharacter_blockTensor_splitCentre F.Carrier
    (fun i => hc (e i)), ?_⟩
  intro a
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ => hx (e i) (a i)

/-- Every actual permuted tensor occurrence has the cone for the same permuted
coordinate vector, including the original individual block weights. -/
theorem permutedCuspidalTensorCone {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    PermutedCuspidalTensorConeStatement.{uF,uV} F T := by
  classical
  let := T.topology
  intro n hn B π hsq C c x hc hx e hsub
  let : ∀ i, Nontrivial (C (e i)).obj := fun i =>
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible
      (C (e i)).obj.representation (C (e i)).property.1
  let b := fun i => Module.Basis.ofVectorSpace ℂ (C (e i)).obj
  let q := fun i => Classical.choice (b i).index_nonempty
  have htensor : Nontrivial (PiTensorProduct ℂ (fun i => (C (e i)).obj)) :=
    ⟨⟨Basis.piTensorProduct b q, 0, (Basis.piTensorProduct b).ne_zero q⟩⟩
  let χ := ∏ i, (c (e i)).comp
    (Pi.evalMonoidHom (fun _ : Fin B.length => F.Carrierˣ) i)
  obtain ⟨hχ, hr⟩ := permutedCuspidalTensorScalar F T n B C c x hc hx e
  exact @squareIntegrableActualJacquetCone.{uF,uV} p _ F T n hn π hsq (B.permute e)
    (FiniteTensor.externalSmoothObject (fun i => (C (e i)).obj))
    htensor hsub χ hχ (x ∘ e) hr

end Langlands
