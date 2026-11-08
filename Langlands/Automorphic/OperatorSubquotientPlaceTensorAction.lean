import Langlands.Automorphic.OperatorSubquotientPlaceCovariance
import Langlands.Automorphic.PlaceEnvelopingTensorAction
import Langlands.Global.ArchimedeanPlaceEnvelopingTensorAdjoint

/-! # Actual two-place enveloping tensor actions on automorphic operator quotients -/

noncomputable section
universe uF

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance quotientPlaceTensorRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance quotientPlaceTensorContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientPlaceTensorSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientPlaceTensorFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance quotientPlaceTensorStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance quotientPlaceTensorRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-- Actual local quotient enveloping operators commute at distinct real places. -/
theorem realPlaceEnvelopingActions_commute (v w : RP) (h : v ≠ w)
    (a b : RealPlaceEnvelopingAlgebra n) :
    Commute (Q.realPlaceEnvelopingAction v a) (Q.realPlaceEnvelopingAction w b) := by
  change Q.envelopingAction (realPlaceEnvelopingInclusion F n v a) *
      Q.envelopingAction (realPlaceEnvelopingInclusion F n w b) =
    Q.envelopingAction (realPlaceEnvelopingInclusion F n w b) *
      Q.envelopingAction (realPlaceEnvelopingInclusion F n v a)
  simpa only [map_mul] using congrArg Q.envelopingAction
    (realPlaceEnvelopingInclusions_commute F n v w h a b).eq

theorem complexPlaceEnvelopingActions_commute (v w : CP) (h : v ≠ w)
    (a b : ComplexPlaceEnvelopingAlgebra n) :
    Commute (Q.complexPlaceEnvelopingAction v a) (Q.complexPlaceEnvelopingAction w b) := by
  change Q.envelopingAction (complexPlaceEnvelopingInclusion F n v a) *
      Q.envelopingAction (complexPlaceEnvelopingInclusion F n w b) =
    Q.envelopingAction (complexPlaceEnvelopingInclusion F n w b) *
      Q.envelopingAction (complexPlaceEnvelopingInclusion F n v a)
  simpa only [map_mul] using congrArg Q.envelopingAction
    (complexPlaceEnvelopingInclusions_commute F n v w h a b).eq

theorem realComplexPlaceEnvelopingActions_commute (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n) (b : ComplexPlaceEnvelopingAlgebra n) :
    Commute (Q.realPlaceEnvelopingAction v a) (Q.complexPlaceEnvelopingAction w b) := by
  change Q.envelopingAction (realPlaceEnvelopingInclusion F n v a) *
      Q.envelopingAction (complexPlaceEnvelopingInclusion F n w b) =
    Q.envelopingAction (complexPlaceEnvelopingInclusion F n w b) *
      Q.envelopingAction (realPlaceEnvelopingInclusion F n v a)
  simpa only [map_mul] using congrArg Q.envelopingAction
    (realComplexPlaceEnvelopingInclusions_commute F n v w a b).eq

/-- The actual two-real-place algebra tensor product acts on the quotient carrier. -/
def realPlacesEnvelopingTensorAction (v w : RP) (h : v ≠ w) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      Module.End ℂ Q.Space :=
  Q.envelopingAction.comp (realPlacesEnvelopingTensorMap F n v w h)

def complexPlacesEnvelopingTensorAction (v w : CP) (h : v ≠ w) :
    (ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      Module.End ℂ Q.Space :=
  Q.envelopingAction.comp (complexPlacesEnvelopingTensorMap F n v w h)

def realComplexPlacesEnvelopingTensorAction (v : RP) (w : CP) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      Module.End ℂ Q.Space :=
  Q.envelopingAction.comp (realComplexPlacesEnvelopingTensorMap F n v w)

/-- Pure tensors act by composition of the two quotient place operators. -/
theorem realPlacesEnvelopingTensorAction_tmul (v w : RP) (h : v ≠ w)
    (a b : RealPlaceEnvelopingAlgebra n) :
    Q.realPlacesEnvelopingTensorAction v w h (a ⊗ₜ[ℂ] b) =
      Q.realPlaceEnvelopingAction v a * Q.realPlaceEnvelopingAction w b := by
  exact (congrArg Q.envelopingAction
    (realPlacesEnvelopingTensorMap_tmul F n v w h a b)).trans
      (Q.envelopingAction.map_mul _ _)

theorem complexPlacesEnvelopingTensorAction_tmul (v w : CP) (h : v ≠ w)
    (a b : ComplexPlaceEnvelopingAlgebra n) :
    Q.complexPlacesEnvelopingTensorAction v w h (a ⊗ₜ[ℂ] b) =
      Q.complexPlaceEnvelopingAction v a * Q.complexPlaceEnvelopingAction w b := by
  exact (congrArg Q.envelopingAction
    (complexPlacesEnvelopingTensorMap_tmul F n v w h a b)).trans
      (Q.envelopingAction.map_mul _ _)

theorem realComplexPlacesEnvelopingTensorAction_tmul (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n) (b : ComplexPlaceEnvelopingAlgebra n) :
    Q.realComplexPlacesEnvelopingTensorAction v w (a ⊗ₜ[ℂ] b) =
      Q.realPlaceEnvelopingAction v a * Q.complexPlaceEnvelopingAction w b := by
  exact (congrArg Q.envelopingAction
    (realComplexPlacesEnvelopingTensorMap_tmul F n v w a b)).trans
      (Q.envelopingAction.map_mul _ _)

/-- On a projected representative, each tensor action is the projected numerator action. -/
@[simp] theorem realPlacesEnvelopingTensorAction_projection (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n)
    (f : Q.upper.Space) :
    Q.realPlacesEnvelopingTensorAction v w h a (Q.projection f) =
      Q.projection (Q.upper.realPlacesEnvelopingTensorAction v w h a f) := rfl

@[simp] theorem complexPlacesEnvelopingTensorAction_projection (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n)
    (f : Q.upper.Space) :
    Q.complexPlacesEnvelopingTensorAction v w h a (Q.projection f) =
      Q.projection (Q.upper.complexPlacesEnvelopingTensorAction v w h a f) := rfl

@[simp] theorem realComplexPlacesEnvelopingTensorAction_projection (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n)
    (f : Q.upper.Space) :
    Q.realComplexPlacesEnvelopingTensorAction v w a (Q.projection f) =
      Q.projection (Q.upper.realComplexPlacesEnvelopingTensorAction v w a f) := rfl

/-- The canonical projection intertwines every two-place tensor algebra element. -/
def realPlacesEnvelopingTensorProjection (v w : RP) (h : v ≠ w) :
    Representation.IntertwiningMap (Q.upper.realPlacesEnvelopingTensorAction v w h).toMonoidHom
      (Q.realPlacesEnvelopingTensorAction v w h).toMonoidHom where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' a :=
    Q.projection.isIntertwining'
      (differentialOperator F n (realPlacesEnvelopingTensorMap F n v w h a))

def complexPlacesEnvelopingTensorProjection (v w : CP) (h : v ≠ w) :
    Representation.IntertwiningMap
      (Q.upper.complexPlacesEnvelopingTensorAction v w h).toMonoidHom
      (Q.complexPlacesEnvelopingTensorAction v w h).toMonoidHom where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' a :=
    Q.projection.isIntertwining'
      (differentialOperator F n (complexPlacesEnvelopingTensorMap F n v w h a))

def realComplexPlacesEnvelopingTensorProjection (v : RP) (w : CP) :
    Representation.IntertwiningMap
      (Q.upper.realComplexPlacesEnvelopingTensorAction v w).toMonoidHom
      (Q.realComplexPlacesEnvelopingTensorAction v w).toMonoidHom where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' a :=
    Q.projection.isIntertwining'
      (differentialOperator F n (realComplexPlacesEnvelopingTensorMap F n v w a))

/-- Every tensor action commutes with every finite adelic translation of the quotient. -/
theorem finiteRepresentation_realPlacesEnvelopingTensorAction
    (d : FiniteAdelicGL F n) (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.realPlacesEnvelopingTensorAction v w h a f) =
      Q.realPlacesEnvelopingTensorAction v w h a (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_envelopingAction d (realPlacesEnvelopingTensorMap F n v w h a) f

theorem finiteRepresentation_complexPlacesEnvelopingTensorAction
    (d : FiniteAdelicGL F n) (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.complexPlacesEnvelopingTensorAction v w h a f) =
      Q.complexPlacesEnvelopingTensorAction v w h a (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_envelopingAction d (complexPlacesEnvelopingTensorMap F n v w h a) f

theorem finiteRepresentation_realComplexPlacesEnvelopingTensorAction
    (d : FiniteAdelicGL F n) (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.realComplexPlacesEnvelopingTensorAction v w a f) =
      Q.realComplexPlacesEnvelopingTensorAction v w a (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_envelopingAction d (realComplexPlacesEnvelopingTensorMap F n v w a) f

/-! Conjugate the quotient tensor actions by actual full compact translation. -/

def realPlacesCompactConjugatedEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      Module.End ℂ Q.Space :=
  (Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)).toAlgHom.comp
    (Q.realPlacesEnvelopingTensorAction v w h)

def complexPlacesCompactConjugatedEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w) :
    (ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      Module.End ℂ Q.Space :=
  (Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)).toAlgHom.comp
    (Q.complexPlacesEnvelopingTensorAction v w h)

def realComplexPlacesCompactConjugatedEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      Module.End ℂ Q.Space :=
  (Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)).toAlgHom.comp
    (Q.realComplexPlacesEnvelopingTensorAction v w)

/-! Full compact covariance holds for every tensor element on the quotient. -/

theorem compactRepresentation_realPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.realPlacesEnvelopingTensorAction v w h a f) =
      Q.realPlacesEnvelopingTensorAction v w h
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℝ n n (p.1 v) (p.1 w) a)
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (Q.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlacesEnvelopingTensorMap F n v w h a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        Q.envelopingAction b
          (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_realPlacesTensorMap F n p v w h a))

theorem compactRepresentation_complexPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.complexPlacesEnvelopingTensorAction v w h a f) =
      Q.complexPlacesEnvelopingTensorAction v w h
        (unitaryMatrixEnvelopingTensorConjugation ℂ ℂ n n (p.2 v) (p.2 w) a)
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (Q.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlacesEnvelopingTensorMap F n v w h a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        Q.envelopingAction b
          (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_complexPlacesTensorMap F n p v w h a))

theorem compactRepresentation_realComplexPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.realComplexPlacesEnvelopingTensorAction v w a f) =
      Q.realComplexPlacesEnvelopingTensorAction v w
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℂ n n (p.1 v) (p.2 w) a)
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (Q.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realComplexPlacesEnvelopingTensorMap F n v w a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        Q.envelopingAction b
          (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_realComplexPlacesTensorMap F n p v w a))

/-! The same covariance as equalities of quotient endomorphisms. -/

theorem compactEndConjugation_realPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) :
    Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.realPlacesEnvelopingTensorAction v w h a) =
      Q.realPlacesEnvelopingTensorAction v w h
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℝ n n (p.1 v) (p.1 w) a) := by
  exact (Q.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlacesEnvelopingTensorMap F n v w h a)).trans
      (congrArg Q.envelopingAction
        (envelopingConjugation_realPlacesTensorMap F n p v w h a))

theorem compactEndConjugation_complexPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) :
    Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.complexPlacesEnvelopingTensorAction v w h a) =
      Q.complexPlacesEnvelopingTensorAction v w h
        (unitaryMatrixEnvelopingTensorConjugation ℂ ℂ n n (p.2 v) (p.2 w) a) := by
  exact (Q.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlacesEnvelopingTensorMap F n v w h a)).trans
      (congrArg Q.envelopingAction
        (envelopingConjugation_complexPlacesTensorMap F n p v w h a))

theorem compactEndConjugation_realComplexPlacesEnvelopingTensorAction
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) :
    Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.realComplexPlacesEnvelopingTensorAction v w a) =
      Q.realComplexPlacesEnvelopingTensorAction v w
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℂ n n (p.1 v) (p.2 w) a) := by
  exact (Q.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realComplexPlacesEnvelopingTensorMap F n v w a)).trans
      (congrArg Q.envelopingAction
        (envelopingConjugation_realComplexPlacesTensorMap F n p v w a))

/-! The conjugated tensor actions equal composition with the actual tensor adjoint. -/

theorem realPlacesCompactConjugatedEnvelopingTensorAction_eq
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w) :
    Q.realPlacesCompactConjugatedEnvelopingTensorAction p v w h =
      (Q.realPlacesEnvelopingTensorAction v w h).comp
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℝ n n (p.1 v) (p.1 w)).toAlgHom := by
  apply AlgHom.ext
  intro a
  exact Q.compactEndConjugation_realPlacesEnvelopingTensorAction p v w h a

theorem complexPlacesCompactConjugatedEnvelopingTensorAction_eq
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w) :
    Q.complexPlacesCompactConjugatedEnvelopingTensorAction p v w h =
      (Q.complexPlacesEnvelopingTensorAction v w h).comp
        (unitaryMatrixEnvelopingTensorConjugation ℂ ℂ n n (p.2 v) (p.2 w)).toAlgHom := by
  apply AlgHom.ext
  intro a
  exact Q.compactEndConjugation_complexPlacesEnvelopingTensorAction p v w h a

theorem realComplexPlacesCompactConjugatedEnvelopingTensorAction_eq
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP) :
    Q.realComplexPlacesCompactConjugatedEnvelopingTensorAction p v w =
      (Q.realComplexPlacesEnvelopingTensorAction v w).comp
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℂ n n (p.1 v) (p.2 w)).toAlgHom := by
  apply AlgHom.ext
  intro a
  exact Q.compactEndConjugation_realComplexPlacesEnvelopingTensorAction p v w a

namespace Equivalence

variable {Q T : OperatorSubquotient F n}

/-- The original quotient equivalence intertwines every two-place tensor action. -/
def realPlacesEnvelopingTensorRestriction (e : Q.Equivalence T) (v w : RP) (h : v ≠ w) :
    Representation.Equiv (Q.realPlacesEnvelopingTensorAction v w h).toMonoidHom
      (T.realPlacesEnvelopingTensorAction v w h).toMonoidHom :=
  Representation.Equiv.mk e.toLinearEquiv (fun a =>
    e.toIntertwiningMap.isIntertwining'
      (differentialOperator F n (realPlacesEnvelopingTensorMap F n v w h a)))

def complexPlacesEnvelopingTensorRestriction (e : Q.Equivalence T) (v w : CP) (h : v ≠ w) :
    Representation.Equiv (Q.complexPlacesEnvelopingTensorAction v w h).toMonoidHom
      (T.complexPlacesEnvelopingTensorAction v w h).toMonoidHom :=
  Representation.Equiv.mk e.toLinearEquiv (fun a =>
    e.toIntertwiningMap.isIntertwining'
      (differentialOperator F n (complexPlacesEnvelopingTensorMap F n v w h a)))

def realComplexPlacesEnvelopingTensorRestriction (e : Q.Equivalence T) (v : RP) (w : CP) :
    Representation.Equiv (Q.realComplexPlacesEnvelopingTensorAction v w).toMonoidHom
      (T.realComplexPlacesEnvelopingTensorAction v w).toMonoidHom :=
  Representation.Equiv.mk e.toLinearEquiv (fun a =>
    e.toIntertwiningMap.isIntertwining'
      (differentialOperator F n (realComplexPlacesEnvelopingTensorMap F n v w a)))

end Equivalence
end OperatorSubquotient
end Langlands.Automorphic
