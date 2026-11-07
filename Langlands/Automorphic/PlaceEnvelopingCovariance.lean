import Langlands.Automorphic.PlaceCompactCovariance
import Langlands.Automorphic.PlaceEnvelopingAction
import Langlands.Global.ArchimedeanPlaceEnvelopingAdjoint

/-! # Actual compact covariance of whole local enveloping actions -/

noncomputable section
universe u

open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ

local instance placeEnvelopingCovarianceRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeEnvelopingCovarianceContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeEnvelopingCovarianceSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeEnvelopingCovarianceFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeEnvelopingCovarianceStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance placeEnvelopingCovarianceSpaceAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _

private theorem realPlaceCompactRepresentation_eq (v : RP) (k : RK) :
    S.realPlaceCompactRepresentation v k =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v k)) := rfl

private theorem complexPlaceCompactRepresentation_eq (v : CP) (k : CK) :
    S.complexPlaceCompactRepresentation v k =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n v k)) := rfl

/-- Conjugate the entire original real-place algebra action by actual compact translation. -/
def realPlaceCompactConjugatedEnvelopingAction (v : RP) (k : RK) :
    RealPlaceEnvelopingAlgebra n →ₐ[ℂ] Module.End ℂ S.Space :=
  (S.realPlaceCompactEndConjugation v k).toAlgHom.comp (S.realPlaceEnvelopingAction v)

def complexPlaceCompactConjugatedEnvelopingAction (v : CP) (k : CK) :
    ComplexPlaceEnvelopingAlgebra n →ₐ[ℂ] Module.End ℂ S.Space :=
  (S.complexPlaceCompactEndConjugation v k).toAlgHom.comp (S.complexPlaceEnvelopingAction v)

/-- Full compact translation acts through the actual selected-place enveloping adjoint. -/
theorem compactRepresentation_realPlaceEnvelopingAction (p : ArchimedeanCompactFactors F n)
    (v : RP) (a : RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.realPlaceEnvelopingAction v a f) =
      S.realPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℝ n (p.1 v) a)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (S.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlaceEnvelopingInclusion F n v a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        S.envelopingAction b
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_realInclusion F n p v a))

theorem compactRepresentation_complexPlaceEnvelopingAction (p : ArchimedeanCompactFactors F n)
    (v : CP) (a : ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.complexPlaceEnvelopingAction v a f) =
      S.complexPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℂ n (p.2 v) a)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (S.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlaceEnvelopingInclusion F n v a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        S.envelopingAction b
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_complexInclusion F n p v a))

/-- The same covariance as equality of original endomorphisms. -/
theorem compactEndConjugation_realPlaceEnvelopingAction (p : ArchimedeanCompactFactors F n)
    (v : RP) (a : RealPlaceEnvelopingAlgebra n) :
    S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.realPlaceEnvelopingAction v a) =
      S.realPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℝ n (p.1 v) a) := by
  exact (S.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlaceEnvelopingInclusion F n v a)).trans
      (congrArg S.envelopingAction (envelopingConjugation_realInclusion F n p v a))

theorem compactEndConjugation_complexPlaceEnvelopingAction (p : ArchimedeanCompactFactors F n)
    (v : CP) (a : ComplexPlaceEnvelopingAlgebra n) :
    S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.complexPlaceEnvelopingAction v a) =
      S.complexPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℂ n (p.2 v) a) := by
  exact (S.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlaceEnvelopingInclusion F n v a)).trans
      (congrArg S.envelopingAction (envelopingConjugation_complexInclusion F n p v a))

/-- The two actual constructions of the conjugated real-place algebra action agree. -/
theorem realPlaceCompactConjugatedEnvelopingAction_eq (v : RP) (k : RK) :
    S.realPlaceCompactConjugatedEnvelopingAction v k =
      (S.realPlaceEnvelopingAction v).comp (unitaryMatrixEnvelopingConjugation ℝ n k).toAlgHom := by
  apply AlgHom.ext
  intro a
  change S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v k))
        (S.realPlaceEnvelopingAction v a) =
      S.realPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℝ n k a)
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_same] using
    S.compactEndConjugation_realPlaceEnvelopingAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) v a

theorem complexPlaceCompactConjugatedEnvelopingAction_eq (v : CP) (k : CK) :
    S.complexPlaceCompactConjugatedEnvelopingAction v k =
      (S.complexPlaceEnvelopingAction v).comp (unitaryMatrixEnvelopingConjugation ℂ n k).toAlgHom := by
  apply AlgHom.ext
  intro a
  change S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k))
        (S.complexPlaceEnvelopingAction v a) =
      S.complexPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℂ n k a)
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_same] using
    S.compactEndConjugation_complexPlaceEnvelopingAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) v a

/-- Same-place compact covariance for every local algebra element. -/
theorem realPlaceCompactRepresentation_realPlaceEnvelopingAction (v : RP) (k : RK)
    (a : RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.realPlaceCompactRepresentation v k (S.realPlaceEnvelopingAction v a f) =
      S.realPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℝ n k a)
        (S.realPlaceCompactRepresentation v k f) := by
  simp only [realPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_same] using
    S.compactRepresentation_realPlaceEnvelopingAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) v a f

theorem complexPlaceCompactRepresentation_complexPlaceEnvelopingAction (v : CP) (k : CK)
    (a : ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.complexPlaceCompactRepresentation v k (S.complexPlaceEnvelopingAction v a f) =
      S.complexPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℂ n k a)
        (S.complexPlaceCompactRepresentation v k f) := by
  simp only [complexPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_same] using
    S.compactRepresentation_complexPlaceEnvelopingAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) v a f

/-- Every real-place compact operator commutes with every complex-place enveloping operator. -/
theorem realPlaceCompactRepresentation_complexPlaceEnvelopingAction (v : RP) (w : CP) (k : RK)
    (a : ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.realPlaceCompactRepresentation v k (S.complexPlaceEnvelopingAction w a f) =
      S.complexPlaceEnvelopingAction w a (S.realPlaceCompactRepresentation v k f) := by
  simp only [realPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_snd,
    unitaryMatrixEnvelopingConjugation_one, AlgEquiv.coe_refl, id_eq] using
    S.compactRepresentation_complexPlaceEnvelopingAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) w a f

theorem complexPlaceCompactRepresentation_realPlaceEnvelopingAction (v : CP) (w : RP) (k : CK)
    (a : RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.complexPlaceCompactRepresentation v k (S.realPlaceEnvelopingAction w a f) =
      S.realPlaceEnvelopingAction w a (S.complexPlaceCompactRepresentation v k f) := by
  simp only [complexPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_fst,
    unitaryMatrixEnvelopingConjugation_one, AlgEquiv.coe_refl, id_eq] using
    S.compactRepresentation_realPlaceEnvelopingAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) w a f

/-- Distinct same-type places also commute on every local algebra element. -/
theorem realPlaceCompactRepresentation_realPlaceEnvelopingAction_of_ne
    (v w : RP) (h : w ≠ v) (k : RK) (a : RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.realPlaceCompactRepresentation v k (S.realPlaceEnvelopingAction w a f) =
      S.realPlaceEnvelopingAction w a (S.realPlaceCompactRepresentation v k f) := by
  simp only [realPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_of_ne h,
    unitaryMatrixEnvelopingConjugation_one, AlgEquiv.coe_refl, id_eq] using
    S.compactRepresentation_realPlaceEnvelopingAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) w a f

theorem complexPlaceCompactRepresentation_complexPlaceEnvelopingAction_of_ne
    (v w : CP) (h : w ≠ v) (k : CK) (a : ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.complexPlaceCompactRepresentation v k (S.complexPlaceEnvelopingAction w a f) =
      S.complexPlaceEnvelopingAction w a (S.complexPlaceCompactRepresentation v k f) := by
  simp only [complexPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_of_ne h,
    unitaryMatrixEnvelopingConjugation_one, AlgEquiv.coe_refl, id_eq] using
    S.compactRepresentation_complexPlaceEnvelopingAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) w a f

end OperatorRealization
end Langlands.Automorphic
