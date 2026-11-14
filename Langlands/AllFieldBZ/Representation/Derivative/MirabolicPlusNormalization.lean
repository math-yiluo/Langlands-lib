import Langlands.AllFieldBZ.Group.GL.MirabolicModulusProof
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicPlus
import Langlands.Representation.Derivative.MirabolicPlusNormalization

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicPlusNormalization`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicPlusNormalization` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ
universe uV uF uG uH

namespace Jacquet
open Langlands.Jacquet
variable {G : Type uG} {H : Type uH} [Group G] [Group H]

end Jacquet
namespace Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding isOpen_ker_phiMinusCharacter isOpen_ker_phiPlusCharacter isOpen_ker_psiMinusCharacter isOpen_ker_psiPlusCharacter isOpen_ker_thetaPlus ker_psiMinusQuotient phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient phiPlusCharacter phiPlusCharacter_eq_inv phiPlusCharacter_mul_phiMinusCharacter plusTwistFunctor psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient psiPlus psiPlusCharacter psiPlusCharacter_eq_inv psiPlusCharacter_mul_psiMinusCharacter psiPlusUnnormalized psiPlus_action psiPlus_levi psiPlus_radical
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic hiding leviRadical_haarCharacter radicalCoordinates_isAddHaar radicalHaar_map_leviConj
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
variable {F : LocalFieldPackage.{uF}}

/-! ## Positive-half characters -/

/-- The `Ψ⁺` normalization character `|det|^(1/2)` on `GL_n`. -/
abbrev psiPlusCharacter (T : F.TopologicalData) (n : ℕ) :
    GeneralLinear n F.Carrier →* ℂˣ :=
  realPowerCharacter (T.determinantNorm n) (1 / 2 : ℝ)

/-- The `Φ⁺` normalization character `|det|^(1/2)` on `P_(n+1)`. -/
abbrev phiPlusCharacter (T : F.TopologicalData) (n : ℕ) :
    mirabolic n F.Carrier →* ℂˣ :=
  realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
    (1 / 2 : ℝ)

theorem isOpen_ker_psiPlusCharacter (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((psiPlusCharacter T n).ker : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact isOpen_ker_realPowerCharacter _ (T.isOpen_ker_determinantNorm n) _

theorem isOpen_ker_phiPlusCharacter (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((phiPlusCharacter T n).ker : Set (mirabolic n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1)
  apply isOpen_ker_realPowerCharacter
  exact (T.isOpen_ker_determinantNorm (n + 1)).preimage continuous_subtype_val

/-- `|det|^(1/2)` is the inverse of the published `Ψ⁻` character `|det|^(-1/2)`. -/
theorem psiPlusCharacter_eq_inv (T : F.TopologicalData) (n : ℕ) :
    psiPlusCharacter T n = (psiMinusCharacter T n)⁻¹ := by
  rw [psiMinusCharacter, realPowerCharacter_neg]
  exact (inv_inv (realPowerCharacter (T.determinantNorm n) (1 / 2 : ℝ))).symm

/-- `|det|^(1/2)` is the inverse of the published `Φ⁻` character `|det|^(-1/2)`. -/
theorem phiPlusCharacter_eq_inv (T : F.TopologicalData) (n : ℕ) :
    phiPlusCharacter T n = (phiMinusCharacter T n)⁻¹ := by
  rw [phiMinusCharacter, realPowerCharacter_neg]
  exact (inv_inv (realPowerCharacter
    ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype) (1 / 2 : ℝ))).symm

theorem psiPlusCharacter_mul_psiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    psiPlusCharacter T n * psiMinusCharacter T n = 1 := by
  rw [psiPlusCharacter_eq_inv]
  exact inv_mul_cancel (psiMinusCharacter T n)

theorem phiPlusCharacter_mul_phiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    phiPlusCharacter T n * phiMinusCharacter T n = 1 := by
  rw [phiPlusCharacter_eq_inv]
  exact inv_mul_cancel (phiMinusCharacter T n)

/-! ## The actual radical Haar positive halves -/

/-! ## Normalized Psi-plus -/

/-- Normalized `Ψ⁺`: twist by `|det|^(1/2)` on `GL_n`, then inflate along the actual
projection `P_(n+1) → GL_n`. -/
def psiPlus (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact SmoothRep.twistFunctor (psiPlusCharacter T n) (isOpen_ker_psiPlusCharacter T n) ⋙
    psiPlusUnnormalized T n

/-- `Ψ⁺(ρ)(g) v = |det(projection g)|^(1/2) ρ(projection g) v`. -/
theorem psiPlus_action (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (g : mirabolic n F.Carrier)
      (v : A), ((psiPlus T n).obj A).representation g v =
        (psiPlusCharacter T n (projection g) : ℂ) • A.representation (projection g) v := by
  intros
  rfl

/-- The radical `V_(n+1)` acts trivially. -/
theorem psiPlus_radical (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (u : radical n F.Carrier)
      (v : A), ((psiPlus T n).obj A).representation (u : mirabolic n F.Carrier) v = v := by
  let := T.topology
  intro A u v
  change (psiPlusCharacter T n (projection (u : mirabolic n F.Carrier)) : ℂ) •
    A.representation (projection (u : mirabolic n F.Carrier)) v = v
  rw [(projection_eq_one_iff _).mpr u.property, map_one, map_one, Units.val_one, one_smul,
    Module.End.one_apply]

/-- The Levi formula `Ψ⁺(ρ)(levi a) = |det a|^(1/2) ρ(a)`. -/
theorem psiPlus_levi (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (a : GeneralLinear n F.Carrier),
      ((psiPlus T n).obj A).representation (levi a) =
        (psiPlusCharacter T n a : ℂ) • A.representation a := by
  let := T.topology
  intro A a
  change (psiPlusCharacter T n (projection (levi a)) : ℂ) •
    A.representation (projection (levi a)) = _
  rw [projection_levi]

/-! ## Normalized Phi-plus -/

end Derivative.Mirabolic
end Langlands.AllFieldBZ
