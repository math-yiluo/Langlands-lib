import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Global.ArchimedeanPlaceCompact

/-! # Single-place compact actions on the original automorphic realization -/

noncomputable section
universe u

open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _
local instance : AddCommGroup T.Space := Submodule.addCommGroup _

/-- Restrict the actual compact action to the orthogonal factor at a real place. -/
def realPlaceCompactRepresentation (v : RP) : Representation ℂ RK S.Space :=
  S.compactRepresentation.comp (realPlaceCompactInclusion F n v).toMonoidHom

/-- Restrict the same action to the unitary factor at a complex place. -/
def complexPlaceCompactRepresentation (v : CP) : Representation ℂ CK S.Space :=
  S.compactRepresentation.comp (complexPlaceCompactInclusion F n v).toMonoidHom

theorem inclusion_realPlaceCompactRepresentation (v : RP) (k : RK) (f : S.Space) :
    S.inclusion (S.realPlaceCompactRepresentation v k f) =
      stableAutomorphicCompactAction F n (realPlaceCompactInclusion F n v k)
        (S.inclusion f) := rfl

theorem inclusion_complexPlaceCompactRepresentation (v : CP) (k : CK) (f : S.Space) :
    S.inclusion (S.complexPlaceCompactRepresentation v k f) =
      stableAutomorphicCompactAction F n (complexPlaceCompactInclusion F n v k)
        (S.inclusion f) := rfl

theorem evaluate_realPlaceCompactRepresentation (v : RP) (k : RK)
    (f : S.Space) (x : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
        (S.toContinuous (S.realPlaceCompactRepresentation v k f)) x =
      ContinuousRationalFunctions.evaluate F n (S.toContinuous f)
        (x * AdelicGL.ofInfinite F n (realPlaceCompactInclusion F n v k).val) := rfl

theorem evaluate_complexPlaceCompactRepresentation (v : CP) (k : CK)
    (f : S.Space) (x : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
        (S.toContinuous (S.complexPlaceCompactRepresentation v k f)) x =
      ContinuousRationalFunctions.evaluate F n (S.toContinuous f)
        (x * AdelicGL.ofInfinite F n (complexPlaceCompactInclusion F n v k).val) := rfl

theorem finiteRepresentation_realPlaceCompactRepresentation
    (d : FiniteAdelicGL F n) (v : RP) (k : RK) (f : S.Space) :
    S.finiteRepresentation d (S.realPlaceCompactRepresentation v k f) =
      S.realPlaceCompactRepresentation v k (S.finiteRepresentation d f) :=
  S.finiteRepresentation_compactRepresentation d (realPlaceCompactInclusion F n v k) f

theorem finiteRepresentation_complexPlaceCompactRepresentation
    (d : FiniteAdelicGL F n) (v : CP) (k : CK) (f : S.Space) :
    S.finiteRepresentation d (S.complexPlaceCompactRepresentation v k f) =
      S.complexPlaceCompactRepresentation v k (S.finiteRepresentation d f) :=
  S.finiteRepresentation_compactRepresentation d (complexPlaceCompactInclusion F n v k) f

/-- A place orbit lies in the original finite-dimensional full compact orbit span. -/
theorem realPlaceCompactRepresentation_isFiniteVector (v : RP) (f : S.Space) :
    FiniteVectors.IsFiniteVector (S.realPlaceCompactRepresentation v) f := by
  have : Module.Finite ℂ (FiniteVectors.orbitSpan S.compactRepresentation f) :=
    S.compactRepresentation_isFiniteVector f
  apply Submodule.finiteDimensional_of_le
    (S₂ := FiniteVectors.orbitSpan S.compactRepresentation f)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact FiniteVectors.action_mem_orbitSpan S.compactRepresentation
    (realPlaceCompactInclusion F n v k) f

theorem complexPlaceCompactRepresentation_isFiniteVector (v : CP) (f : S.Space) :
    FiniteVectors.IsFiniteVector (S.complexPlaceCompactRepresentation v) f := by
  have : Module.Finite ℂ (FiniteVectors.orbitSpan S.compactRepresentation f) :=
    S.compactRepresentation_isFiniteVector f
  apply Submodule.finiteDimensional_of_le
    (S₂ := FiniteVectors.orbitSpan S.compactRepresentation f)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact FiniteVectors.action_mem_orbitSpan S.compactRepresentation
    (complexPlaceCompactInclusion F n v k) f

/-- Covariance retains the actual global adjoint of the inserted compact element. -/
theorem realPlaceCompactRepresentation_complexLieAction (v : RP) (k : RK)
    (X : ArchimedeanGL.ComplexLieAlgebra F n) (f : S.Space) :
    S.realPlaceCompactRepresentation v k (S.complexLieAction X f) =
      S.complexLieAction
        (ArchimedeanGL.complexLieConjugation F n
          (realPlaceCompactInclusion F n v k).val X)
        (S.realPlaceCompactRepresentation v k f) :=
  S.compactRepresentation_complexLieAction (realPlaceCompactInclusion F n v k) X f

theorem complexPlaceCompactRepresentation_complexLieAction (v : CP) (k : CK)
    (X : ArchimedeanGL.ComplexLieAlgebra F n) (f : S.Space) :
    S.complexPlaceCompactRepresentation v k (S.complexLieAction X f) =
      S.complexLieAction
        (ArchimedeanGL.complexLieConjugation F n
          (complexPlaceCompactInclusion F n v k).val X)
        (S.complexPlaceCompactRepresentation v k f) :=
  S.compactRepresentation_complexLieAction (complexPlaceCompactInclusion F n v k) X f

namespace Intertwiner

variable {S T}

/-- A full intertwiner retains its original map on each real compact factor. -/
def realPlaceCompactRestriction (A : S.Intertwiner T) (v : RP) :
    (S.realPlaceCompactRepresentation v).IntertwiningMap
      (T.realPlaceCompactRepresentation v) where
  toLinearMap := A.toLinearMap
  isIntertwining' k := A.isIntertwining' (compactOperator F n (realPlaceCompactInclusion F n v k))

def complexPlaceCompactRestriction (A : S.Intertwiner T) (v : CP) :
    (S.complexPlaceCompactRepresentation v).IntertwiningMap
      (T.complexPlaceCompactRepresentation v) where
  toLinearMap := A.toLinearMap
  isIntertwining' k :=
    A.isIntertwining' (compactOperator F n (complexPlaceCompactInclusion F n v k))

end Intertwiner

namespace Equivalence

variable {S T}

/-- A full equivalence retains its original linear equivalence on each place action. -/
def realPlaceCompactRestriction (e : S.Equivalence T) (v : RP) :
    (S.realPlaceCompactRepresentation v).Equiv (T.realPlaceCompactRepresentation v) :=
  Representation.Equiv.mk e.toLinearEquiv (fun k =>
    e.toIntertwiningMap.isIntertwining' (compactOperator F n (realPlaceCompactInclusion F n v k)))

def complexPlaceCompactRestriction (e : S.Equivalence T) (v : CP) :
    (S.complexPlaceCompactRepresentation v).Equiv (T.complexPlaceCompactRepresentation v) :=
  Representation.Equiv.mk e.toLinearEquiv (fun k =>
    e.toIntertwiningMap.isIntertwining' (compactOperator F n (complexPlaceCompactInclusion F n v k)))

end Equivalence
end OperatorRealization
end Langlands.Automorphic
