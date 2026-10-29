import Langlands.Group.GL.MirabolicModulusProof
import Langlands.Representation.Derivative.MirabolicMinus

/-!
# Haar normalization of the actual mirabolic minus functors

The canonical inverse half of the radical Haar character agrees with the
determinant real-power characters used by the published minus functors.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands

universe uG uH uF uV

namespace Jacquet

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- The positive square root and the positive real power define the same
complex character. -/
theorem positiveHalfCharacter_eq_realPowerCharacter (δ : G →* ℝ≥0ˣ) :
    complexCharacter (positiveHalfCharacter δ) =
      realPowerCharacter δ (1 / 2 : ℝ) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp only [complexCharacter_apply, positiveHalfCharacter_apply,
    coe_realPowerCharacter, Real.coe_sqrt, Real.sqrt_eq_rpow]

/-- The canonical inverse half is the negative one-half real power. -/
theorem inverseHalfCharacter_eq_realPowerCharacter (δ : G →* ℝ≥0ˣ) :
    inverseHalfCharacter δ = realPowerCharacter δ (-(1 / 2 : ℝ)) := by
  rw [realPowerCharacter_neg]
  exact congrArg Inv.inv (positiveHalfCharacter_eq_realPowerCharacter δ)

/-- Canonical inverse halves commute with restriction along a homomorphism. -/
theorem inverseHalfCharacter_comp (δ : G →* ℝ≥0ˣ) (φ : H →* G) :
    (inverseHalfCharacter δ).comp φ = inverseHalfCharacter (δ.comp φ) := by
  rfl

end Jacquet

namespace Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The inverse half of actual radical Haar modulus, restricted through the
standard Levi equivalence to `GL_n`. -/
def psiMinusHaarInverseHalf (T : F.TopologicalData) (n : ℕ) :
    GeneralLinear n F.Carrier →* ℂˣ := by
  letI := T.topology
  letI := T.fieldT2
  letI := T.generalLinearTopologicalGroup (n + 1)
  letI := T.generalLinearLocallyCompactSpace (n + 1)
  letI := locallyCompactSpace (n := n) (F := F.Carrier)
  exact (HaarModulus.closedInverseHalfCharacter (radical n F.Carrier)
    radical_isClosed (leviSubgroup n F.Carrier) leviSubgroup_le_normalizer).comp
    (leviEquiv (n := n) (F := F.Carrier)).toMonoidHom

/-- The inverse half of actual radical Haar modulus, restricted through the
successor equivalence to `P_(n+1)`. -/
def phiMinusHaarInverseHalf (T : F.TopologicalData) (n : ℕ) :
    mirabolic n F.Carrier →* ℂˣ := by
  letI := T.topology
  letI := T.fieldT2
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  letI := T.generalLinearLocallyCompactSpace (n + 1 + 1)
  letI := locallyCompactSpace (n := n + 1) (F := F.Carrier)
  exact (HaarModulus.closedInverseHalfCharacter (radical (n + 1) F.Carrier)
    radical_isClosed (successorSubgroup n F.Carrier)
    successorSubgroup_le_normalizer).comp
    (successorEquiv (n := n) (F := F.Carrier)).toMonoidHom

/-- The actual Haar inverse half agrees with the published `Ψ⁻` character. -/
theorem psiMinusHaarInverseHalf_eq (T : F.TopologicalData) (n : ℕ) :
    psiMinusHaarInverseHalf T n = psiMinusCharacter T n := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := locallyCompactSpace (n := n) (F := F.Carrier)
  change (Jacquet.inverseHalfCharacter
    (HaarModulus.closedRestrictCharacter (radical n F.Carrier)
      radical_isClosed (leviSubgroup n F.Carrier) leviSubgroup_le_normalizer)).comp
      (leviEquiv (n := n) (F := F.Carrier)).toMonoidHom = _
  rw [Jacquet.inverseHalfCharacter_comp, leviRadical_haarCharacter F T n,
    Jacquet.inverseHalfCharacter_eq_realPowerCharacter]

/-- The actual Haar inverse half agrees with the published `Φ⁻` character. -/
theorem phiMinusHaarInverseHalf_eq (T : F.TopologicalData) (n : ℕ) :
    phiMinusHaarInverseHalf T n = phiMinusCharacter T n := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1 + 1)
  let := locallyCompactSpace (n := n + 1) (F := F.Carrier)
  change (Jacquet.inverseHalfCharacter
    (HaarModulus.closedRestrictCharacter (radical (n + 1) F.Carrier)
      radical_isClosed (successorSubgroup n F.Carrier)
      successorSubgroup_le_normalizer)).comp
      (successorEquiv (n := n) (F := F.Carrier)).toMonoidHom = _
  rw [Jacquet.inverseHalfCharacter_comp, successorRadical_haarCharacter F T n,
    Jacquet.inverseHalfCharacter_eq_realPowerCharacter]

theorem isOpen_ker_psiMinusHaarInverseHalf (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((psiMinusHaarInverseHalf T n).ker : Set (GeneralLinear n F.Carrier)) := by
  rw [psiMinusHaarInverseHalf_eq]
  exact isOpen_ker_psiMinusCharacter T n

theorem isOpen_ker_phiMinusHaarInverseHalf (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((phiMinusHaarInverseHalf T n).ker : Set (mirabolic n F.Carrier)) := by
  rw [phiMinusHaarInverseHalf_eq]
  exact isOpen_ker_phiMinusCharacter T n

/-- Equality of actual `Ψ⁻` functors with normalization by the radical Haar
inverse half, including their quotient-induced maps. -/
theorem psiMinus_haarNormalization (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    psiMinus.{uV} T n = psiMinusUnnormalized T n ⋙
      SmoothRep.twistFunctor (psiMinusHaarInverseHalf T n)
        (isOpen_ker_psiMinusHaarInverseHalf T n) := by
  simp only [psiMinusHaarInverseHalf_eq]
  rfl

/-- Equality of actual `Φ⁻` functors with normalization by the radical Haar
inverse half, including their quotient-induced maps. -/
theorem phiMinus_haarNormalization (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiMinus.{uV} T ψ n = phiMinusUnnormalized T ψ n ⋙
      SmoothRep.twistFunctor (phiMinusHaarInverseHalf T n)
        (isOpen_ker_phiMinusHaarInverseHalf T n) := by
  simp only [phiMinusHaarInverseHalf_eq]
  rfl

end Derivative.Mirabolic

end Langlands
