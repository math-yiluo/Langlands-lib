import Langlands.Representation.RankinSelberg.RankOneExtensionDivisibilityStatement
import Langlands.Representation.Induction.OppositeProductReversalProof
import Langlands.Representation.Shahidi.TensorBridge

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

@[simp] theorem reverse_twice {n : ℕ} (B : BlockShape n) : B.reverse.reverse = B := by
  cases B with
  | mk l s hp he =>
    have hs : (fun i : Fin l => s i.rev.rev) = s := by
      funext i
      rw [Fin.rev_rev]
    simp only [reverse, hs]

end Langlands.GeneralLinear.BlockShape

namespace Langlands.RankinSelberg

open GeneralLinear

universe uF uW

abbrev rankOneExtensionUpperShape (t : ℕ) : BlockShape (1 + (t + 1)) :=
  Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t)

abbrev rankOneExtensionLowerShape (t : ℕ) : BlockShape (1 + (t + 1)) :=
  (rankOneExtensionUpperShape t).reverse

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (t : ℕ)
  (χ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) (ULift.{uW} ℂ))
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)

abbrev rankOneExtensionLowerCarrier (i : Fin 2) : Type uW :=
  Shahidi.pairCarrier (ULift.{uW} ℂ) W i.rev

abbrev rankOneExtensionLowerFamily (i : Fin 2) :
    Representation ℂ (Langlands.GeneralLinear ((rankOneExtensionLowerShape t).size i)
      F.Carrier) (rankOneExtensionLowerCarrier (W := W) i) :=
  Shahidi.pairFamily χ σ i.rev

abbrev rankOneExtensionLowerInduced :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (1 + (t + 1))
  letI : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  letI : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      Module ℂ (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  F.canonicalTopologicalData.normalizedOppositeParabolicInduced
    (rankOneExtensionLowerShape t)
    (V := PiTensorProduct ℂ (rankOneExtensionLowerCarrier (W := W)))
    ((rankOneExtensionLowerShape t).blockTensor
      (V := rankOneExtensionLowerCarrier (W := W)) (rankOneExtensionLowerFamily F t χ σ))

theorem rankOneExtensionLowerToUpperEquiv
    (hχ : letI := F.canonicalTopologicalData.topology; IsSmooth χ)
    (hσ : letI := F.canonicalTopologicalData.topology; IsSmooth σ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (1 + (t + 1))
    Nonempty (Representation.Equiv (rankOneExtensionLowerInduced F t χ σ)
      (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
        (Shahidi.pairFamily χ σ))) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (1 + (t + 1))
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      Module ℂ (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  have hs : ∀ i, IsSmooth (rankOneExtensionLowerFamily F t χ σ i) := by
    intro i
    fin_cases i
    · exact hσ
    · exact hχ
  obtain ⟨E, _hE, _hEinv⟩ := glOppositeProductReversal p F F.canonicalTopologicalData
    (1 + (t + 1)) (rankOneExtensionLowerShape t)
    (rankOneExtensionLowerCarrier (W := W)) (rankOneExtensionLowerFamily F t χ σ) hs
  let Q (e : Equiv.Perm (Fin 2)) : Prop :=
    let B : BlockShape (1 + (t + 1)) :=
      { length := 2
        size := fun i => (rankOneExtensionUpperShape t).size (e i)
        positive := fun i => (rankOneExtensionUpperShape t).positive (e i)
        sum_eq := (Equiv.sum_comp e (rankOneExtensionUpperShape t).size).trans
          (rankOneExtensionUpperShape t).sum_eq }
    letI : ∀ i : Fin 2, AddCommGroup (Shahidi.pairCarrier (ULift.{uW} ℂ) W (e i)) :=
      fun i => Shahidi.pairCarrier.instAddCommGroup (e i)
    letI : ∀ i : Fin 2, Module ℂ (Shahidi.pairCarrier (ULift.{uW} ℂ) W (e i)) :=
      fun i => Shahidi.pairCarrier.instModule ℂ (e i)
    Nonempty (Representation.Equiv (rankOneExtensionLowerInduced F t χ σ)
      (F.canonicalTopologicalData.normalizedProductInduced B
        (V := fun i => Shahidi.pairCarrier (ULift.{uW} ℂ) W (e i))
        (fun i => Shahidi.pairFamily χ σ (e i))))
  have hQ : Q (Fin.revPerm.trans Fin.revPerm) := ⟨E⟩
  have he : (Fin.revPerm.trans Fin.revPerm : Equiv.Perm (Fin 2)) = Equiv.refl _ := by
    apply Equiv.ext
    intro i
    exact Fin.rev_rev i
  rw [he] at hQ
  exact hQ

end Langlands.RankinSelberg
