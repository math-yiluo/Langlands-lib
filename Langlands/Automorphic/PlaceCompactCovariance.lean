import Langlands.Automorphic.PlaceLieAction
import Langlands.Automorphic.PlaceCompactAction
import Langlands.Global.ArchimedeanPlaceAdjoint

/-! # Actual place compact and Lie covariance on automorphic realizations -/

noncomputable section
universe u v

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL

private theorem unitaryMatrixComplexLieConjugation_one_apply
    (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) :
    unitaryMatrixComplexLieConjugation 𝕜 n 1 X = X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp
  | add X Y hX hY => simp only [map_add, hX, hY]

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

local instance placeCompactCovarianceRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeCompactCovarianceContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeCompactCovarianceSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeCompactCovarianceFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeCompactCovarianceStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance placeCompactCovarianceSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _

private theorem realPlaceCompactRepresentation_eq (v : RP) (k : RK) :
    S.realPlaceCompactRepresentation v k =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v k)) := rfl

private theorem complexPlaceCompactRepresentation_eq (v : CP) (k : CK) :
    S.complexPlaceCompactRepresentation v k =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n v k)) := rfl

/-- Full compact translation acts on each real-place Lie algebra by its actual matrix adjoint. -/
theorem compactRepresentation_realPlaceLieAction (p : ArchimedeanCompactFactors F n)
    (v : RP) (X : ℂ ⊗[ℝ] RM) (f : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.realPlaceLieAction v X f) =
      S.realPlaceLieAction v (unitaryMatrixComplexLieConjugation ℝ n (p.1 v) X)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (S.compactRepresentation_complexLieAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlaceComplexLieInclusion F n v X) f).trans
      (congrArg (fun Y : ComplexLieAlgebra F n =>
        S.complexLieAction Y
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (complexLieConjugation_realInclusion F n p v X))

theorem compactRepresentation_complexPlaceLieAction (p : ArchimedeanCompactFactors F n)
    (v : CP) (X : ℂ ⊗[ℝ] CM) (f : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.complexPlaceLieAction v X f) =
      S.complexPlaceLieAction v (unitaryMatrixComplexLieConjugation ℂ n (p.2 v) X)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (S.compactRepresentation_complexLieAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlaceComplexLieInclusion F n v X) f).trans
      (congrArg (fun Y : ComplexLieAlgebra F n =>
        S.complexLieAction Y
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (complexLieConjugation_complexInclusion F n p v X))

/-- Same-place covariance on the original automorphic vectors. -/
theorem realPlaceCompactRepresentation_realPlaceLieAction (v : RP) (k : RK)
    (X : ℂ ⊗[ℝ] RM) (f : S.Space) :
    S.realPlaceCompactRepresentation v k (S.realPlaceLieAction v X f) =
      S.realPlaceLieAction v (unitaryMatrixComplexLieConjugation ℝ n k X)
        (S.realPlaceCompactRepresentation v k f) := by
  simp only [realPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_same] using
    S.compactRepresentation_realPlaceLieAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) v X f

theorem complexPlaceCompactRepresentation_complexPlaceLieAction (v : CP) (k : CK)
    (X : ℂ ⊗[ℝ] CM) (f : S.Space) :
    S.complexPlaceCompactRepresentation v k (S.complexPlaceLieAction v X f) =
      S.complexPlaceLieAction v (unitaryMatrixComplexLieConjugation ℂ n k X)
        (S.complexPlaceCompactRepresentation v k f) := by
  simp only [complexPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_same] using
    S.compactRepresentation_complexPlaceLieAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) v X f

/-- Compact translation at a real place commutes with every complex-place Lie action. -/
theorem realPlaceCompactRepresentation_complexPlaceLieAction (v : RP) (w : CP) (k : RK)
    (X : ℂ ⊗[ℝ] CM) (f : S.Space) :
    S.realPlaceCompactRepresentation v k (S.complexPlaceLieAction w X f) =
      S.complexPlaceLieAction w X (S.realPlaceCompactRepresentation v k f) := by
  simp only [realPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_snd,
    unitaryMatrixComplexLieConjugation_one_apply] using
    S.compactRepresentation_complexPlaceLieAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) w X f

theorem complexPlaceCompactRepresentation_realPlaceLieAction (v : CP) (w : RP) (k : CK)
    (X : ℂ ⊗[ℝ] RM) (f : S.Space) :
    S.complexPlaceCompactRepresentation v k (S.realPlaceLieAction w X f) =
      S.realPlaceLieAction w X (S.complexPlaceCompactRepresentation v k f) := by
  simp only [complexPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_fst,
    unitaryMatrixComplexLieConjugation_one_apply] using
    S.compactRepresentation_realPlaceLieAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) w X f

/-- At distinct real places the actual compact and Lie operators commute. -/
theorem realPlaceCompactRepresentation_realPlaceLieAction_of_ne
    (v w : RP) (h : w ≠ v) (k : RK) (X : ℂ ⊗[ℝ] RM) (f : S.Space) :
    S.realPlaceCompactRepresentation v k (S.realPlaceLieAction w X f) =
      S.realPlaceLieAction w X (S.realPlaceCompactRepresentation v k f) := by
  simp only [realPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_fst,
    Pi.mulSingle_eq_of_ne h, unitaryMatrixComplexLieConjugation_one_apply] using
    S.compactRepresentation_realPlaceLieAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) w X f

theorem complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne
    (v w : CP) (h : w ≠ v) (k : CK) (X : ℂ ⊗[ℝ] CM) (f : S.Space) :
    S.complexPlaceCompactRepresentation v k (S.complexPlaceLieAction w X f) =
      S.complexPlaceLieAction w X (S.complexPlaceCompactRepresentation v k f) := by
  simp only [complexPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_snd,
    Pi.mulSingle_eq_of_ne h, unitaryMatrixComplexLieConjugation_one_apply] using
    S.compactRepresentation_complexPlaceLieAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) w X f

/-- Actual orthogonal place translation conjugates endomorphisms on the original carrier. -/
def realPlaceCompactEndConjugation (v : RP) (k : RK) :
    Module.End ℂ S.Space ≃ₐ[ℂ] Module.End ℂ S.Space :=
  S.compactEndConjugation (realPlaceCompactInclusion F n v k)

def complexPlaceCompactEndConjugation (v : CP) (k : CK) :
    Module.End ℂ S.Space ≃ₐ[ℂ] Module.End ℂ S.Space :=
  S.compactEndConjugation (complexPlaceCompactInclusion F n v k)

theorem realPlaceCompactEndConjugation_finite (v : RP) (k : RK)
    (d : FiniteAdelicGL F n) :
    S.realPlaceCompactEndConjugation v k (S.finiteRepresentation d) =
      S.finiteRepresentation d :=
  S.compactEndConjugation_finite (realPlaceCompactInclusion F n v k) d

theorem complexPlaceCompactEndConjugation_finite (v : CP) (k : CK)
    (d : FiniteAdelicGL F n) :
    S.complexPlaceCompactEndConjugation v k (S.finiteRepresentation d) =
      S.finiteRepresentation d :=
  S.compactEndConjugation_finite (complexPlaceCompactInclusion F n v k) d

end OperatorRealization
end Langlands.Automorphic
