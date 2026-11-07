import Langlands.Automorphic.OperatorSubquotientArchimedean
import Langlands.Automorphic.PlaceEnvelopingCovariance

/-! # Actual archimedean place actions on automorphic operator quotients -/

noncomputable section
universe uF

open scoped Classical

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
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ

local instance quotientPlaceRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientPlaceContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientPlaceSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientPlaceFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance quotientPlaceStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientPlaceRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-- Orthogonal translation at a real place on the original module quotient. -/
def realPlaceCompactRepresentation (v : RP) : Representation ℂ RK Q.Space :=
  Q.compactRepresentation.comp (realPlaceCompactInclusion F n v).toMonoidHom

/-- Unitary translation at a complex place on the same original quotient. -/
def complexPlaceCompactRepresentation (v : CP) : Representation ℂ CK Q.Space :=
  Q.compactRepresentation.comp (complexPlaceCompactInclusion F n v).toMonoidHom

/-- Restrict the quotient's genuine differential through the real-place inclusion. -/
def realPlaceEnvelopingAction (v : RP) :
    RealPlaceEnvelopingAlgebra n →ₐ[ℂ] Module.End ℂ Q.Space :=
  Q.envelopingAction.comp (realPlaceEnvelopingInclusion F n v)

/-- The complex-place domain retains the full underlying real matrix Lie algebra. -/
def complexPlaceEnvelopingAction (v : CP) :
    ComplexPlaceEnvelopingAlgebra n →ₐ[ℂ] Module.End ℂ Q.Space :=
  Q.envelopingAction.comp (complexPlaceEnvelopingInclusion F n v)

/-- The canonical projection intertwines the genuine real-place compact actions. -/
def realPlaceCompactProjection (v : RP) :
    (Q.upper.realPlaceCompactRepresentation v).IntertwiningMap
      (Q.realPlaceCompactRepresentation v) where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' k :=
    Q.projection.isIntertwining' (compactOperator F n (realPlaceCompactInclusion F n v k))

def complexPlaceCompactProjection (v : CP) :
    (Q.upper.complexPlaceCompactRepresentation v).IntertwiningMap
      (Q.complexPlaceCompactRepresentation v) where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' k :=
    Q.projection.isIntertwining' (compactOperator F n (complexPlaceCompactInclusion F n v k))

/-- The same projection intertwines every element of the local enveloping algebra. -/
def realPlaceEnvelopingProjection (v : RP) :
    Representation.IntertwiningMap (Q.upper.realPlaceEnvelopingAction v).toMonoidHom
      (Q.realPlaceEnvelopingAction v).toMonoidHom where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' a :=
    Q.projection.isIntertwining'
      (differentialOperator F n (realPlaceEnvelopingInclusion F n v a))

def complexPlaceEnvelopingProjection (v : CP) :
    Representation.IntertwiningMap (Q.upper.complexPlaceEnvelopingAction v).toMonoidHom
      (Q.complexPlaceEnvelopingAction v).toMonoidHom where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' a :=
    Q.projection.isIntertwining'
      (differentialOperator F n (complexPlaceEnvelopingInclusion F n v a))

@[simp] theorem realPlaceCompactRepresentation_projection
    (v : RP) (k : RK) (f : Q.upper.Space) :
    Q.realPlaceCompactRepresentation v k (Q.projection f) =
      Q.projection (Q.upper.realPlaceCompactRepresentation v k f) := rfl

@[simp] theorem complexPlaceCompactRepresentation_projection
    (v : CP) (k : CK) (f : Q.upper.Space) :
    Q.complexPlaceCompactRepresentation v k (Q.projection f) =
      Q.projection (Q.upper.complexPlaceCompactRepresentation v k f) := rfl

@[simp] theorem realPlaceEnvelopingAction_projection
    (v : RP) (a : RealPlaceEnvelopingAlgebra n) (f : Q.upper.Space) :
    Q.realPlaceEnvelopingAction v a (Q.projection f) =
      Q.projection (Q.upper.realPlaceEnvelopingAction v a f) := rfl

@[simp] theorem complexPlaceEnvelopingAction_projection
    (v : CP) (a : ComplexPlaceEnvelopingAlgebra n) (f : Q.upper.Space) :
    Q.complexPlaceEnvelopingAction v a (Q.projection f) =
      Q.projection (Q.upper.complexPlaceEnvelopingAction v a f) := rfl

/-- A local quotient orbit span is exactly the image of the local numerator orbit span. -/
theorem map_realPlaceCompactOrbitSpan (v : RP) (f : Q.upper.Space) :
    (FiniteVectors.orbitSpan (Q.upper.realPlaceCompactRepresentation v) f).map
        Q.projection.toLinearMap =
      FiniteVectors.orbitSpan (Q.realPlaceCompactRepresentation v) (Q.projection f) :=
  FiniteVectors.map_orbitSpan (Q.realPlaceCompactProjection v) f

theorem map_complexPlaceCompactOrbitSpan (v : CP) (f : Q.upper.Space) :
    (FiniteVectors.orbitSpan (Q.upper.complexPlaceCompactRepresentation v) f).map
        Q.projection.toLinearMap =
      FiniteVectors.orbitSpan (Q.complexPlaceCompactRepresentation v) (Q.projection f) :=
  FiniteVectors.map_orbitSpan (Q.complexPlaceCompactProjection v) f

/-- Every quotient vector remains finite for the actual real-place compact action. -/
theorem realPlaceCompactRepresentation_isFiniteVector (v : RP) (f : Q.Space) :
    FiniteVectors.IsFiniteVector (Q.realPlaceCompactRepresentation v) f := by
  obtain ⟨g, rfl⟩ := Q.projection_surjective f
  exact (Q.upper.realPlaceCompactRepresentation_isFiniteVector v g).map
    (Q.realPlaceCompactProjection v)

theorem complexPlaceCompactRepresentation_isFiniteVector (v : CP) (f : Q.Space) :
    FiniteVectors.IsFiniteVector (Q.complexPlaceCompactRepresentation v) f := by
  obtain ⟨g, rfl⟩ := Q.projection_surjective f
  exact (Q.upper.complexPlaceCompactRepresentation_isFiniteVector v g).map
    (Q.complexPlaceCompactProjection v)

theorem finiteRepresentation_realPlaceCompactRepresentation
    (d : FiniteAdelicGL F n) (v : RP) (k : RK) (f : Q.Space) :
    Q.finiteRepresentation d (Q.realPlaceCompactRepresentation v k f) =
      Q.realPlaceCompactRepresentation v k (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_compactRepresentation d (realPlaceCompactInclusion F n v k) f

theorem finiteRepresentation_complexPlaceCompactRepresentation
    (d : FiniteAdelicGL F n) (v : CP) (k : CK) (f : Q.Space) :
    Q.finiteRepresentation d (Q.complexPlaceCompactRepresentation v k f) =
      Q.complexPlaceCompactRepresentation v k (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_compactRepresentation d (complexPlaceCompactInclusion F n v k) f

theorem finiteRepresentation_realPlaceEnvelopingAction (d : FiniteAdelicGL F n)
    (v : RP) (a : RealPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.realPlaceEnvelopingAction v a f) =
      Q.realPlaceEnvelopingAction v a (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_envelopingAction d (realPlaceEnvelopingInclusion F n v a) f

theorem finiteRepresentation_complexPlaceEnvelopingAction (d : FiniteAdelicGL F n)
    (v : CP) (a : ComplexPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.complexPlaceEnvelopingAction v a f) =
      Q.complexPlaceEnvelopingAction v a (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_envelopingAction d (complexPlaceEnvelopingInclusion F n v a) f

set_option maxHeartbeats 800000 in
/-- Actual matrix adjoint covariance descends on every real-place enveloping element. -/
theorem realPlaceCompactRepresentation_realPlaceEnvelopingAction (v : RP) (k : RK)
    (a : RealPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.realPlaceCompactRepresentation v k (Q.realPlaceEnvelopingAction v a f) =
      Q.realPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℝ n k a)
        (Q.realPlaceCompactRepresentation v k f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro g
  change Q.projection
      (Q.upper.realPlaceCompactRepresentation v k (Q.upper.realPlaceEnvelopingAction v a g)) =
    Q.projection
      (Q.upper.realPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℝ n k a)
        (Q.upper.realPlaceCompactRepresentation v k g))
  exact congrArg Q.projection
    (Q.upper.realPlaceCompactRepresentation_realPlaceEnvelopingAction v k a g)

set_option maxHeartbeats 800000 in
theorem complexPlaceCompactRepresentation_complexPlaceEnvelopingAction (v : CP) (k : CK)
    (a : ComplexPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.complexPlaceCompactRepresentation v k (Q.complexPlaceEnvelopingAction v a f) =
      Q.complexPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℂ n k a)
        (Q.complexPlaceCompactRepresentation v k f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro g
  change Q.projection
      (Q.upper.complexPlaceCompactRepresentation v k
        (Q.upper.complexPlaceEnvelopingAction v a g)) =
    Q.projection
      (Q.upper.complexPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℂ n k a)
        (Q.upper.complexPlaceCompactRepresentation v k g))
  exact congrArg Q.projection
    (Q.upper.complexPlaceCompactRepresentation_complexPlaceEnvelopingAction v k a g)

namespace Equivalence

variable {Q T : OperatorSubquotient F n}

/-- The original quotient equivalence also intertwines each actual compact restriction. -/
def realPlaceCompactRestriction (e : Q.Equivalence T) (v : RP) :
    (Q.realPlaceCompactRepresentation v).Equiv (T.realPlaceCompactRepresentation v) :=
  Representation.Equiv.mk e.toLinearEquiv (fun k =>
    e.toIntertwiningMap.isIntertwining'
      (compactOperator F n (realPlaceCompactInclusion F n v k)))

def complexPlaceCompactRestriction (e : Q.Equivalence T) (v : CP) :
    (Q.complexPlaceCompactRepresentation v).Equiv (T.complexPlaceCompactRepresentation v) :=
  Representation.Equiv.mk e.toLinearEquiv (fun k =>
    e.toIntertwiningMap.isIntertwining'
      (compactOperator F n (complexPlaceCompactInclusion F n v k)))

/-- The same linear equivalence intertwines every original local differential. -/
def realPlaceEnvelopingRestriction (e : Q.Equivalence T) (v : RP) :
    Representation.Equiv (Q.realPlaceEnvelopingAction v).toMonoidHom
      (T.realPlaceEnvelopingAction v).toMonoidHom :=
  Representation.Equiv.mk e.toLinearEquiv (fun a =>
    e.toIntertwiningMap.isIntertwining'
      (differentialOperator F n (realPlaceEnvelopingInclusion F n v a)))

def complexPlaceEnvelopingRestriction (e : Q.Equivalence T) (v : CP) :
    Representation.Equiv (Q.complexPlaceEnvelopingAction v).toMonoidHom
      (T.complexPlaceEnvelopingAction v).toMonoidHom :=
  Representation.Equiv.mk e.toLinearEquiv (fun a =>
    e.toIntertwiningMap.isIntertwining'
      (differentialOperator F n (complexPlaceEnvelopingInclusion F n v a)))

end Equivalence
end OperatorSubquotient
end Langlands.Automorphic
