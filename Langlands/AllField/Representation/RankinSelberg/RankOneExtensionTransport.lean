import Langlands.Representation.RankinSelberg.RankOneExtensionTransport
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Induction.OppositeProductReversalProof
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionDivisibilityStatement
import Langlands.AllField.Representation.Shahidi.IntertwiningCovariance
noncomputable section

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape hiding HasBlockIwahoriFactorization IsWeaklyContracting
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerToUpperEquiv
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uW

variable (F : Type uF) [Field F]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (t : ℕ)
  (χ : Representation ℂ (Langlands.GeneralLinear 1 F) (ULift.{uW} ℂ))
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)

abbrev rankOneExtensionLowerFamily (i : Fin 2) :
    Representation ℂ (Langlands.GeneralLinear ((rankOneExtensionLowerShape t).size i)
      F) (rankOneExtensionLowerCarrier (W := W) i) :=
  Shahidi.pairFamily χ σ i.rev

abbrev rankOneExtensionLowerInduced [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :=
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (1 + (t + 1))
  letI : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  letI : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      Module ℂ (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced
    (rankOneExtensionLowerShape t)
    (V := PiTensorProduct ℂ (rankOneExtensionLowerCarrier (W := W)))
    ((rankOneExtensionLowerShape t).blockTensor
      (V := rankOneExtensionLowerCarrier (W := W)) (rankOneExtensionLowerFamily F t χ σ))

theorem rankOneExtensionLowerToUpperEquiv [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (hχ : IsSmooth χ)
    (hσ : IsSmooth σ) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (1 + (t + 1))
    Nonempty (Representation.Equiv (rankOneExtensionLowerInduced F t χ σ)
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (rankOneExtensionUpperShape t)
        (Shahidi.pairFamily χ σ))) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (1 + (t + 1))
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
  obtain ⟨E, _hE, _hEinv⟩ := glOppositeProductReversal F (⟨⟩ : LocalFieldData F)
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
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced B
        (V := fun i => Shahidi.pairCarrier (ULift.{uW} ℂ) W (e i))
        (fun i => Shahidi.pairFamily χ σ (e i))))
  have hQ : Q (Fin.revPerm.trans Fin.revPerm) := ⟨E⟩
  have he : (Fin.revPerm.trans Fin.revPerm : Equiv.Perm (Fin 2)) = Equiv.refl _ := by
    apply Equiv.ext
    intro i
    exact Fin.rev_rev i
  rw [he] at hQ
  exact hQ

end Langlands.AllField.RankinSelberg
