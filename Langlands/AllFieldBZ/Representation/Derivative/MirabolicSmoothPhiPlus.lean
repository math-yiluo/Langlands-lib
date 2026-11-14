import Langlands.AllFieldBZ.Representation.Derivative.MirabolicPlusNormalization
import Langlands.AllFieldBZ.Representation.Induction.Equivalences
import Langlands.Representation.Derivative.MirabolicSmoothPhiPlus

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicSmoothPhiPlus`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicSmoothPhiPlus` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding isOpen_ker_phiMinusCharacter isOpen_ker_phiPlusCharacter isOpen_ker_psiMinusCharacter isOpen_ker_psiPlusCharacter isOpen_ker_thetaPlus ker_psiMinusQuotient phiHatPlus phiHatPlusEval phiHatPlusEval_covariant phiHatPlusEval_injective phiHatPlusEval_radical_mul phiHatPlusEval_successor_mul phiHatPlusNormalizedEval phiHatPlusNormalizedEval_injective phiHatPlusNormalizedEval_radical_mul phiHatPlusNormalizedEval_successor_mul phiHatPlusUnnormalized phiHatPlus_action phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient phiPlusCharacter phiPlusCharacter_eq_inv phiPlusCharacter_mul_phiMinusCharacter plusTwistFunctor psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient psiPlus psiPlusCharacter psiPlusCharacter_eq_inv psiPlusCharacter_mul_psiMinusCharacter psiPlusUnnormalized psiPlus_action psiPlus_levi psiPlus_radical
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic hiding leviRadical_haarCharacter radicalCoordinates_isAddHaar radicalHaar_map_leviConj
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uV uF

variable {F : LocalFieldPackage.{uF}}

/-! ## Unnormalized smooth Phi-plus -/

/-- Unnormalized `Φ̂⁺(τ) = Ind(P_(n+2), Q, τ')`: actual smooth induction from the plus
subgroup `Q`, by right translation and without a support condition. -/
def phiHatPlusUnnormalized (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact plusTwistFunctor T ψ n ⋙ SmoothRep.toRep ⋙
    Induction.smoothInductionFunctor (plusSubgroup n F.Carrier)

/-- Evaluation of a vector of `Φ̂⁺(τ)` at a point of `P_(n+2)`. -/
abbrev phiHatPlusEval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (phiHatPlusUnnormalized T ψ n).obj τ → mirabolic (n + 1) F.Carrier → τ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact fun τ φ x => Induction.eval (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation)
    (show Induction.SmoothFunctions (plusSubgroup n F.Carrier)
      (plusTwistRepresentation ψ n τ.representation) from φ) x

/-- Vectors of `Φ̂⁺(τ)` are determined by their values. -/
theorem phiHatPlusEval_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      Function.Injective (phiHatPlusEval T ψ n τ) := by
  let := T.topology
  intro τ φ φ' h
  exact Subtype.ext (Subtype.ext h)

/-- Covariance `φ(q x) = thetaPlus(q) • τ(plusProjection q) φ(x)` for `q ∈ Q`. -/
theorem phiHatPlusEval_covariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (q : plusSubgroup n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ φ ((q : mirabolic (n + 1) F.Carrier) * x) =
        (thetaPlus ψ n q : ℂ) •
          τ.representation (plusProjection q) (phiHatPlusEval T ψ n τ φ x) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ φ q x
  exact (show Induction.SmoothFunctions (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation) from φ).1.2 q x

/-- Radical elements act on values through `Θ`. -/
theorem phiHatPlusEval_radical_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (u : radical (n + 1) F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ φ (u.val * x) = (theta ψ n u : ℂ) • phiHatPlusEval T ψ n τ φ x := by
  let := T.topology
  intro τ φ u x
  have h := phiHatPlusEval_covariant T ψ n τ φ (plusRadical u) x
  rw [thetaPlus_plusRadical, plusProjection_plusRadical, map_one, Module.End.one_apply] at h
  exact h

/-- Successor elements act on values through `τ`. -/
theorem phiHatPlusEval_successor_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlusUnnormalized T ψ n).obj τ) (g : mirabolic n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusEval T ψ n τ φ (successor g * x) =
        τ.representation g (phiHatPlusEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ g x
  have h := phiHatPlusEval_covariant T ψ n τ φ (plusSuccessor g) x
  rw [thetaPlus_plusSuccessor, plusProjection_plusSuccessor, Units.val_one, one_smul] at h
  exact h

/-! ## Normalized smooth Phi-plus -/

/-- Normalized `Φ̂⁺`: twist by `|det|^(1/2)` on `P_(n+1)`, then apply the actual
unnormalized smooth induction from the plus subgroup `Q = P_(n+1) V_(n+2)`. This is the
normalization of the published compact `Φ⁺`. -/
def phiHatPlus (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier) := by
  letI := T.topology
  exact SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n) ⋙
    phiHatPlusUnnormalized T ψ n

/-- Evaluation of a vector of normalized `Φ̂⁺(τ)` at a point of `P_(n+2)`. -/
abbrev phiHatPlusNormalizedEval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (phiHatPlus T ψ n).obj τ → mirabolic (n + 1) F.Carrier → τ := by
  letI := T.topology
  exact fun τ => phiHatPlusEval T ψ n
    ((SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n)).obj τ)

/-- Vectors of normalized `Φ̂⁺(τ)` are determined by their values. -/
theorem phiHatPlusNormalizedEval_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      Function.Injective (phiHatPlusNormalizedEval T ψ n τ) := by
  let := T.topology
  intro τ
  exact phiHatPlusEval_injective T ψ n _

/-- Radical elements act on values through `Θ`. -/
theorem phiHatPlusNormalizedEval_radical_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlus T ψ n).obj τ) (u : radical (n + 1) F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n τ φ (u.val * x) =
        (theta ψ n u : ℂ) • phiHatPlusNormalizedEval T ψ n τ φ x := by
  let := T.topology
  intro τ φ u x
  exact phiHatPlusEval_radical_mul T ψ n _ φ u x

/-- Successor elements act on values through `|det|^(1/2) τ`. -/
theorem phiHatPlusNormalizedEval_successor_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiHatPlus T ψ n).obj τ) (g : mirabolic n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n τ φ (successor g * x) =
        (phiPlusCharacter T n g : ℂ) •
          τ.representation g (phiHatPlusNormalizedEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ g x
  exact phiHatPlusEval_successor_mul T ψ n _ φ g x

/-- The action is right translation: `(g • φ)(x) = φ(x g)`. -/
theorem phiHatPlus_action (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : mirabolic (n + 1) F.Carrier)
      (φ : (phiHatPlus T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n τ (((phiHatPlus T ψ n).obj τ).representation g φ) x =
        phiHatPlusNormalizedEval T ψ n τ φ (x * g) := by
  intros
  rfl

/-! ## The compact `Φ⁺` inside the smooth `Φ̂⁺` -/

end Langlands.AllFieldBZ.Derivative.Mirabolic
