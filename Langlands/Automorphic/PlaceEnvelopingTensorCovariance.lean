import Langlands.Automorphic.PlaceEnvelopingTensorAction
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Global.ArchimedeanPlaceEnvelopingTensorAdjoint

/-! # Compact covariance of actual two-place enveloping tensor actions -/

noncomputable section
universe u

open scoped Classical TensorProduct

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

local instance placeEnvelopingTensorCovarianceRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeEnvelopingTensorCovarianceContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeEnvelopingTensorCovarianceSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeEnvelopingTensorCovarianceFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeEnvelopingTensorCovarianceStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance placeEnvelopingTensorCovarianceSpaceAddCommGroup :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-! Conjugate the original tensor actions by the actual full compact translation. -/

def realPlacesCompactConjugatedEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) →ₐ[ℂ] Module.End ℂ S.Space :=
  (S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)).toAlgHom.comp
    (S.realPlacesEnvelopingTensorAction v w h)

def complexPlacesCompactConjugatedEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w) :
    (ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ] Module.End ℂ S.Space :=
  (S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)).toAlgHom.comp
    (S.complexPlacesEnvelopingTensorAction v w h)

def realComplexPlacesCompactConjugatedEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ] Module.End ℂ S.Space :=
  (S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)).toAlgHom.comp
    (S.realComplexPlacesEnvelopingTensorAction v w)

/-! Full compact covariance holds for every tensor element on the unchanged carrier. -/

theorem compactRepresentation_realPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.realPlacesEnvelopingTensorAction v w h a f) =
      S.realPlacesEnvelopingTensorAction v w h
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℝ n n (p.1 v) (p.1 w) a)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (S.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlacesEnvelopingTensorMap F n v w h a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        S.envelopingAction b
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_realPlacesTensorMap F n p v w h a))

theorem compactRepresentation_complexPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.complexPlacesEnvelopingTensorAction v w h a f) =
      S.complexPlacesEnvelopingTensorAction v w h
        (unitaryMatrixEnvelopingTensorConjugation ℂ ℂ n n (p.2 v) (p.2 w) a)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (S.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlacesEnvelopingTensorMap F n v w h a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        S.envelopingAction b
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_complexPlacesTensorMap F n p v w h a))

theorem compactRepresentation_realComplexPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.realComplexPlacesEnvelopingTensorAction v w a f) =
      S.realComplexPlacesEnvelopingTensorAction v w
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℂ n n (p.1 v) (p.2 w) a)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (S.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realComplexPlacesEnvelopingTensorMap F n v w a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        S.envelopingAction b
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_realComplexPlacesTensorMap F n p v w a))

/-! The same covariance identifies conjugation of the original endomorphisms. -/

theorem compactEndConjugation_realPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) :
    S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.realPlacesEnvelopingTensorAction v w h a) =
      S.realPlacesEnvelopingTensorAction v w h
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℝ n n (p.1 v) (p.1 w) a) := by
  exact (S.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlacesEnvelopingTensorMap F n v w h a)).trans
      (congrArg S.envelopingAction
        (envelopingConjugation_realPlacesTensorMap F n p v w h a))

theorem compactEndConjugation_complexPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) :
    S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.complexPlacesEnvelopingTensorAction v w h a) =
      S.complexPlacesEnvelopingTensorAction v w h
        (unitaryMatrixEnvelopingTensorConjugation ℂ ℂ n n (p.2 v) (p.2 w) a) := by
  exact (S.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlacesEnvelopingTensorMap F n v w h a)).trans
      (congrArg S.envelopingAction
        (envelopingConjugation_complexPlacesTensorMap F n p v w h a))

theorem compactEndConjugation_realComplexPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) :
    S.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (S.realComplexPlacesEnvelopingTensorAction v w a) =
      S.realComplexPlacesEnvelopingTensorAction v w
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℂ n n (p.1 v) (p.2 w) a) := by
  exact (S.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realComplexPlacesEnvelopingTensorMap F n v w a)).trans
      (congrArg S.envelopingAction
        (envelopingConjugation_realComplexPlacesTensorMap F n p v w a))

/-! The constructed conjugated action equals composition by the actual tensor adjoint. -/

theorem realPlacesCompactConjugatedEnvelopingTensorAction_eq
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w) :
    S.realPlacesCompactConjugatedEnvelopingTensorAction p v w h =
      (S.realPlacesEnvelopingTensorAction v w h).comp
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℝ n n (p.1 v) (p.1 w)).toAlgHom := by
  apply AlgHom.ext
  intro a
  exact S.compactEndConjugation_realPlacesEnvelopingTensorAction p v w h a

theorem complexPlacesCompactConjugatedEnvelopingTensorAction_eq
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w) :
    S.complexPlacesCompactConjugatedEnvelopingTensorAction p v w h =
      (S.complexPlacesEnvelopingTensorAction v w h).comp
        (unitaryMatrixEnvelopingTensorConjugation ℂ ℂ n n (p.2 v) (p.2 w)).toAlgHom := by
  apply AlgHom.ext
  intro a
  exact S.compactEndConjugation_complexPlacesEnvelopingTensorAction p v w h a

theorem realComplexPlacesCompactConjugatedEnvelopingTensorAction_eq
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP) :
    S.realComplexPlacesCompactConjugatedEnvelopingTensorAction p v w =
      (S.realComplexPlacesEnvelopingTensorAction v w).comp
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℂ n n (p.1 v) (p.2 w)).toAlgHom := by
  apply AlgHom.ext
  intro a
  exact S.compactEndConjugation_realComplexPlacesEnvelopingTensorAction p v w a

end OperatorRealization
end Langlands.Automorphic
