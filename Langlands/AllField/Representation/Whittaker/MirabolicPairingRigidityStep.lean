import Langlands.Representation.Whittaker.MirabolicPairingRigidityStep
import Langlands.AllField.Representation.Derivative.MirabolicMinusIrreducibleStatement
import Langlands.AllField.Representation.Derivative.MirabolicMinusPairingTransferStatement
import Langlands.AllField.Representation.Smooth.SmallRealizationProof
import Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement
/-!
# The induction step of mirabolic twisted pairing rigidity

The radical-generated case of `MirabolicTwistedPairingRigidityStatement` in rank
`m + 2` is reduced to rank `m + 1` through the unnormalized Bernstein–Zelevinsky
functor `Φ⁻` of the Library. The reduction uses two statements about `Φ⁻`
(`PhiMinusIrreducibleStatement` and `PhiMinusPairingTransferStatement`) and the
functional multiplicity statement in ranks `m + 1` and `m + 2`.
-/

noncomputable section

namespace Langlands.AllField.Whittaker.MirabolicRigidity
open Langlands.Whittaker.MirabolicRigidity hiding exists_functional_ne_zero_of_phiMinus nonempty_equiv_of_phiMinus
open Langlands.AllField.Whittaker.MirabolicRigidity
open Langlands.Whittaker hiding MirabolicFunctionalMultiplicityStatement
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV uW

/-! ### Elementary lemmas -/

section Elementary

variable {G : Type*} [Monoid G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

end Elementary

/-! ### Transfer of Whittaker functionals through `Φ⁻` -/

section Transfer

open Langlands.GeneralLinear.Mirabolic

variable {F : Type uF} [CommRing F]

variable [TopologicalSpace F]

end Transfer

section PadicTransfer

open Langlands.GeneralLinear.Mirabolic

variable {F : Type uF} [Field F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A nonzero Whittaker functional on `Φ⁻ ξ` gives a nonzero Whittaker functional on `ξ`. -/
theorem exists_functional_ne_zero_of_phiMinus (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ξ : Representation ℂ (mirabolic (m + 1) F) V) (hs : IsSmooth ξ)
      (ℓ : functionals (Mirabolic.upperUnipotent m F) (mirabolicCharacter ψ m)
        ((Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ hs)).representation),
      ℓ ≠ 0 →
        ∃ ℓ' : functionals (Mirabolic.upperUnipotent (m + 1) F) (mirabolicCharacter ψ (m + 1)) ξ,
          ℓ' ≠ 0 := by
  let := T.topology
  intro ψ ξ hs ℓ hℓ
  let A := SmoothRep.of ξ hs
  let q := Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient T ψ m A
  refine ⟨⟨ℓ.val.comp q, ?_⟩, ?_⟩
  · intro n v
    change ℓ.val (q (ξ (n : mirabolic (m + 1) F) v)) = _ * ℓ.val (q v)
    rw [upperUnipotent_eq_radicalElement_mul_successor n, map_mul, Module.End.mul_apply]
    have h1 := Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient_radical T ψ m A
      (radicalElement (lastColumn n.val)) (ξ (successor (upperUnipotentBlock n).val) v)
    have h2 : q (ξ (successor (upperUnipotentBlock n).val) v) =
        ((Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj A).representation
          (upperUnipotentBlock n).val (q v) := rfl
    change ℓ.val (q (ξ (radicalElement (lastColumn n.val)).val
      (ξ (successor (upperUnipotentBlock n).val) v))) = _
    rw [h1]
    refine (ℓ.val.map_smul _ _).trans ?_
    rw [smul_eq_mul]
    change _ * ℓ.val (q (ξ (successor (upperUnipotentBlock n).val) v)) = _
    rw [h2, ℓ.property (upperUnipotentBlock n) (q v), mirabolicCharacter_succ, mul_assoc]
    rfl
  · have hℓ' : ℓ.val ≠ 0 := fun h => hℓ (Subtype.ext h)
    intro h0
    apply hℓ'
    apply LinearMap.ext
    intro y
    obtain ⟨v, rfl⟩ := Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient_surjective T ψ m A y
    exact congrArg (fun f : functionals (Mirabolic.upperUnipotent (m + 1) F)
      (mirabolicCharacter ψ (m + 1)) ξ => f.val v) h0

end PadicTransfer

/-! ### Recognition through `Φ⁻` -/

section Recognition

variable {F : Type uF} [Field F]

/-- If `Φ⁻ ξ` is irreducible and equivalent to the compact model in rank `m + 1`,
then `ξ` is equivalent to the compact model in rank `m + 2`. -/
theorem nonempty_equiv_of_phiMinus (T : LocalFieldData F) (m : ℕ)
    (hM : MirabolicFunctionalMultiplicityStatement.{uF, uV} F T m)
    (hN : MirabolicFunctionalMultiplicityStatement.{uF, uV} F T (m + 1)) :
    letI := T.topology
    letI : IsTopologicalRing F := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ξ : Representation ℂ (mirabolic (m + 1) F) V) (hs : IsSmooth ξ),
      ξ.IsIrreducible →
      ((Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj
        (SmoothRep.of ξ hs)).representation.IsIrreducible →
      Nonempty (((Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj
        (SmoothRep.of ξ hs)).representation.Equiv (mirabolicCompactInduced ψ m)) →
      Nonempty (ξ.Equiv (mirabolicCompactInduced ψ (m + 1))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ ξ hs hirr hXi he
  let X := (Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ hs)
  obtain ⟨eL⟩ := (hM ψ X X.representation X.isSmooth hXi).2.1.mpr he
  have hℓ : eL.symm 1 ≠ 0 := by
    intro h
    have := congrArg eL h
    simp at this
  obtain ⟨ℓ', hℓ'⟩ := exists_functional_ne_zero_of_phiMinus T m ψ ξ hs (eL.symm 1) hℓ
  have hN1 := hN ψ V ξ hs hirr
  exact hN1.2.1.mp (nonempty_linearEquiv_of_multiples hℓ' (fun ℓ'' => hN1.1 ℓ' ℓ'' hℓ'))

end Recognition

/-! ### The induction step -/

end Langlands.AllField.Whittaker.MirabolicRigidity
