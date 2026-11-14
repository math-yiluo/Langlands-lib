import Langlands.AllFieldBZ.Group.GL.MirabolicProjection
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinus
import Langlands.Representation.Derivative.MirabolicPlus

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicPlus`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicPlus` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter isOpen_ker_thetaPlus ker_psiMinusQuotient phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient plusTwistFunctor psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient psiPlusUnnormalized
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis
universe uV uF

/-! ## The positive character on the plus subgroup -/

section Character
variable {F : Type uF} [CommRing F] {n : ℕ}

variable [TopologicalSpace F]

/-! ## The twisted plus-subgroup representation -/

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Character
variable {F : LocalFieldPackage.{uF}}

/-- The kernel of `thetaPlus` is open for every supplied p-adic topology. -/
theorem isOpen_ker_thetaPlus (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    IsOpen ((thetaPlus ψ n).ker : Set (plusSubgroup n F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : NonarchimedeanGroup (GeneralLinear (n + 1 + 1) F.Carrier) :=
    valuativeGeneralLinearNonarchimedean F.Carrier (n + 1 + 1)
  exact thetaPlus_isOpen_ker ψ

/-! ## Unnormalized Psi-plus -/

/-- Unnormalized `Ψ⁺`: inflate along the actual projection `P_(n+1) → GL_n`, so that
`Ψ⁺(ρ)(g) = ρ(projection g)` on the same carrier. -/
def psiPlusUnnormalized (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact continuousPullbackFunctor projection continuous_projection

/-! ## The functor `τ ↦ τ'` -/

/-- `τ ↦ τ'`: inflate along `plusProjection`, then twist by `thetaPlus`. -/
def plusTwistFunctor (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (plusSubgroup n F.Carrier) := by
  letI := T.topology
  exact continuousPullbackFunctor plusProjection continuous_plusProjection ⋙
    SmoothRep.twistFunctor (thetaPlus ψ n) (isOpen_ker_thetaPlus T ψ n)

/-! ## Unnormalized Phi-plus -/

end Langlands.AllFieldBZ.Derivative.Mirabolic
