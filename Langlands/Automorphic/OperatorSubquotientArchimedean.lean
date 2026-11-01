import Langlands.Automorphic.OperatorSubquotient
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Automorphic.DifferentialCenterFinite

/-! # Compact covariance and center finiteness on actual automorphic quotients -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientArchRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientArchContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientArchSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientArchFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance quotientArchStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientArchRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

/-- Restriction of the genuine enveloping action to its actual center. -/
def centerAction :
    ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] Module.End ℂ S.Space :=
  S.envelopingAction.comp (ArchimedeanGL.centerInclusion F n)

/-- The multiplicative representation underlying the same center algebra action. -/
def centerRepresentation : Representation ℂ (ArchimedeanGL.EnvelopingCenter F n) S.Space :=
  S.centerAction.toMonoidHom

/-- The actual finite-smooth function of a realized vector, with center covariance. -/
def centerAmbientInclusion :
    S.centerRepresentation.IntertwiningMap (finiteSmoothCenterRepresentation F n) where
  toLinearMap := (automorphicFiniteSmoothInclusion F n).toLinearMap.comp
    S.formInclusion.toLinearMap
  isIntertwining' _ := by ext; rfl

theorem centerAmbientInclusion_injective : Function.Injective S.centerAmbientInclusion :=
  (automorphicFiniteSmoothInclusion_injective F n).comp S.formInclusion_injective

/-- Faithful inclusion reflects exactly the simultaneous finiteness of all slices. -/
theorem centerRepresentation_isFiniteVector_iff (f : S.Space) :
    FiniteVectors.IsFiniteVector S.centerRepresentation f ↔
      IsCenterFinite F n (finiteSmoothInclusion F n (S.centerAmbientInclusion f)) :=
  (FiniteVectors.isFiniteVector_map_iff S.centerAmbientInclusion
    S.centerAmbientInclusion_injective f).symm.trans
      (isCenterFinite_iff_finiteSmoothCenterVector F n _).symm

/-- Each realized vector has one finite span for the entire actual center. -/
theorem centerRepresentation_isFiniteVector (f : S.Space) :
    FiniteVectors.IsFiniteVector S.centerRepresentation f := by
  apply (S.centerRepresentation_isFiniteVector_iff f).mpr
  exact (((mem_automorphicSubrepresentation F n (S.formInclusion f).val).mp
    (S.formInclusion f).property).2.2.1)

end OperatorRealization

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-- The canonical quotient projection for the actual compact actions. -/
def compactProjection : Q.upper.compactRepresentation.IntertwiningMap Q.compactRepresentation where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' k := Q.projection.isIntertwining' (compactOperator F n k)

/-- The quotient compact orbit span is precisely the projected numerator orbit span. -/
theorem map_compactOrbitSpan (f : Q.upper.Space) :
    (FiniteVectors.orbitSpan Q.upper.compactRepresentation f).map Q.projection.toLinearMap =
      FiniteVectors.orbitSpan Q.compactRepresentation (Q.projection f) :=
  FiniteVectors.map_orbitSpan Q.compactProjection f

theorem compactRepresentation_isFiniteVector (f : Q.Space) :
    FiniteVectors.IsFiniteVector Q.compactRepresentation f := by
  obtain ⟨v, rfl⟩ := Q.projection_surjective f
  exact (Q.upper.compactRepresentation_isFiniteVector v).map Q.compactProjection

set_option maxHeartbeats 800000 in
/-- The finite and compact actions commute on the actual quotient. -/
theorem finiteRepresentation_compactRepresentation
    (d : FiniteAdelicGL F n) (k : standardInfiniteCompact F n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.compactRepresentation k f) =
      Q.compactRepresentation k (Q.finiteRepresentation d f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro v
  change Q.projection (Q.upper.finiteRepresentation d (Q.upper.compactRepresentation k v)) =
    Q.projection (Q.upper.compactRepresentation k (Q.upper.finiteRepresentation d v))
  exact congrArg Q.projection (Q.upper.finiteRepresentation_compactRepresentation d k v)

set_option maxHeartbeats 800000 in
/-- The actual adjoint covariance descends without adding a covariance hypothesis. -/
theorem compactRepresentation_envelopingAction (k : standardInfiniteCompact F n)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : Q.Space) :
    Q.compactRepresentation k (Q.envelopingAction a f) =
      Q.envelopingAction (ArchimedeanGL.envelopingConjugation F n k.val a)
        (Q.compactRepresentation k f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro v
  change Q.projection (Q.upper.compactRepresentation k (Q.upper.envelopingAction a v)) =
    Q.projection (Q.upper.envelopingAction (ArchimedeanGL.envelopingConjugation F n k.val a)
      (Q.upper.compactRepresentation k v))
  exact congrArg Q.projection (Q.upper.compactRepresentation_envelopingAction k a v)

/-- Actual compact translation is invertible on the module quotient. -/
def compactLinearEquiv (k : standardInfiniteCompact F n) : Q.Space ≃ₗ[ℂ] Q.Space :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (Q.compactRepresentation.asGroupHom k)

@[simp] theorem compactLinearEquiv_apply (k : standardInfiniteCompact F n) (f : Q.Space) :
    Q.compactLinearEquiv k f = Q.compactRepresentation k f := rfl

@[simp] theorem compactLinearEquiv_symm_apply (k : standardInfiniteCompact F n) (f : Q.Space) :
    (Q.compactLinearEquiv k).symm f = Q.compactRepresentation k⁻¹ f := rfl

/-- The same compact operator is an automorphism of the finite quotient representation. -/
def compactFiniteEquivalence (k : standardInfiniteCompact F n) :
    Q.finiteRepresentation.Equiv Q.finiteRepresentation :=
  Representation.Equiv.mk (Q.compactLinearEquiv k)
    (fun d => LinearMap.ext (fun f =>
      (Q.finiteRepresentation_compactRepresentation d k f).symm))

/-- The genuine quotient enveloping action restricted to the actual center. -/
def centerAction :
    ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] Module.End ℂ Q.Space :=
  Q.envelopingAction.comp (ArchimedeanGL.centerInclusion F n)

def centerRepresentation : Representation ℂ (ArchimedeanGL.EnvelopingCenter F n) Q.Space :=
  Q.centerAction.toMonoidHom

/-- The canonical projection retains the entire genuine center action. -/
def centerProjection : Q.upper.centerRepresentation.IntertwiningMap Q.centerRepresentation where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' z :=
    Q.projection.isIntertwining' (differentialOperator F n (ArchimedeanGL.centerInclusion F n z))

@[simp] theorem centerAction_projection (z : ArchimedeanGL.EnvelopingCenter F n)
    (f : Q.upper.Space) :
    Q.centerAction z (Q.projection f) = Q.projection (Q.upper.centerAction z f) := rfl

/-- The full center orbit, not separately finite slices, is an exact projected image. -/
theorem map_centerOrbitSpan (f : Q.upper.Space) :
    (FiniteVectors.orbitSpan Q.upper.centerRepresentation f).map Q.projection.toLinearMap =
      FiniteVectors.orbitSpan Q.centerRepresentation (Q.projection f) :=
  FiniteVectors.map_orbitSpan Q.centerProjection f

theorem centerRepresentation_isFiniteVector (f : Q.Space) :
    FiniteVectors.IsFiniteVector Q.centerRepresentation f := by
  obtain ⟨v, rfl⟩ := Q.projection_surjective f
  exact (Q.upper.centerRepresentation_isFiniteVector v).map Q.centerProjection

/-- Finite translation commutes with this same genuine center action. -/
theorem finiteRepresentation_centerAction (d : FiniteAdelicGL F n)
    (z : ArchimedeanGL.EnvelopingCenter F n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.centerAction z f) =
      Q.centerAction z (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_envelopingAction d (ArchimedeanGL.centerInclusion F n z) f

set_option maxHeartbeats 800000 in
/-- The quotient algebra action retains central commutation with every differential. -/
theorem envelopingAction_centerAction (a : ArchimedeanGL.EnvelopingAlgebra F n)
    (z : ArchimedeanGL.EnvelopingCenter F n) (f : Q.Space) :
    Q.envelopingAction a (Q.centerAction z f) =
      Q.centerAction z (Q.envelopingAction a f) := by
  change Q.envelopingAction a
      (Q.envelopingAction (ArchimedeanGL.centerInclusion F n z) f) =
    Q.envelopingAction (ArchimedeanGL.centerInclusion F n z) (Q.envelopingAction a f)
  calc
    _ = Q.envelopingAction (a * ArchimedeanGL.centerInclusion F n z) f :=
      (congrArg (fun m : Module.End ℂ Q.Space => m f)
        (Q.envelopingAction.map_mul a (ArchimedeanGL.centerInclusion F n z))).symm
    _ = Q.envelopingAction (ArchimedeanGL.centerInclusion F n z * a) f :=
      congrArg (fun b : ArchimedeanGL.EnvelopingAlgebra F n => Q.envelopingAction b f)
        (ArchimedeanGL.centerInclusion_commute F n z a)
    _ = _ := congrArg (fun m : Module.End ℂ Q.Space => m f)
      (Q.envelopingAction.map_mul (ArchimedeanGL.centerInclusion F n z) a)

end OperatorSubquotient
end Langlands.Automorphic
