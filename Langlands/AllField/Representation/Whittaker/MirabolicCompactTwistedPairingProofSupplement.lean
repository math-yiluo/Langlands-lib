import Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.AllField.Representation.Shahidi.Induction
import Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProof
import Langlands.AllField.Representation.Whittaker.MirabolicPairingStatementSupplement
/-!
# The compact mirabolic twisted pairing is one-dimensional

For a p-adic field, every unitary additive character `ψ`, every rank `n` and
every `s : ℂ`, the space of bilinear forms `B` on the actual compact mirabolic
model with `B (τ g f₁) (τ g f₂) = |det g|^(-s) B f₁ f₂` is linearly equivalent to `ℂ`.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicCompactTwistedPairingStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement mirabolicCompactTwistedPairing
open Langlands.AllField.Whittaker

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis
open Langlands.Induction hiding SmoothRep
open Langlands.QuotientIntegration
open scoped ENNReal

universe uF

namespace MirabolicCompactTwistedPairing
open Langlands.Whittaker.MirabolicCompactTwistedPairing hiding isOpenNormOne_normalizedAbsoluteValue
open Langlands.AllField.Whittaker.MirabolicCompactTwistedPairing
open Langlands.Whittaker hiding MirabolicCompactTwistedPairingStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement mirabolicCompactTwistedPairing
open Langlands.AllField.Whittaker

section Generic



end Generic

end MirabolicCompactTwistedPairing

open Langlands.Whittaker.MirabolicCompactTwistedPairing hiding isOpenNormOne_normalizedAbsoluteValue
open Langlands.AllField.Whittaker.MirabolicCompactTwistedPairing

/-- The actual compact mirabolic twisted pairing is one-dimensional. -/
theorem mirabolicCompactTwistedPairing (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) : MirabolicCompactTwistedPairingStatement.{uF} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have := valuative_nonarchimedean (K := F)
  have : ∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F) :=
    T.generalLinearNonarchimedean
  have : ∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F) :=
    T.generalLinearLocallyCompactSpace
  intro ψ s
  have hstd : IsOpen ((standardCharacter ψ n).ker :
      Set (GeneralLinear.upperUnipotent (n + 1) F)) := by
    have := T.upperUnipotentNonarchimedean (n + 1)
    exact isOpen_ker_of_continuous_complex_character _ (standardCharacterContinuous ψ n).continuous
  have hker : IsOpen ((mirabolicCharacter ψ n).ker : Set (Mirabolic.upperUnipotent n F)) :=
    hstd.preimage Mirabolic.upperUnipotentContinuousEquiv.continuous
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (Mirabolic.upperUnipotent n F)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
    (Mirabolic.upperUnipotent n F)) := ⟨rfl⟩
  have hν := MirabolicQuotient.exists_measure (F := F) n
  have := hν.choose_spec.1
  let eX := (nonempty_oppositeForms_equiv ψ n hker hν.choose hν.choose_spec.2.1
    hν.choose_spec.2.2).some
  exact ⟨(mirabolicFormsDeterminantShift (isOpenNormOne_normalizedAbsoluteValue T) ψ n
    (mirabolicCompactInduced ψ n) (-s) _ (fun _ => (1 : ℂ)) (fun _ => (mul_one _).symm)).trans
    ((InvariantBilinear.equivRight _ _ (mirabolicCharacterChangeEquiv ψ (-1) n)).trans eX)⟩

end Langlands.AllField.Whittaker
