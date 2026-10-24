import Langlands.Global.ArchimedeanCenterFinite
import Langlands.Global.ArchimedeanCompactLieAlgebra

/-! # Joint center and compact enveloping orbits of smooth functions -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Restriction of the actual differential action to the compact enveloping subalgebra. -/
def compactEnvelopingAction :
    compactEnvelopingSubalgebra K n →ₐ[ℂ] Module.End ℂ (SmoothFunctions K n) :=
  (envelopingAction K n).comp (compactEnvelopingSubalgebra K n).val

@[simp]
theorem compactEnvelopingAction_apply (b : compactEnvelopingSubalgebra K n) :
    compactEnvelopingAction K n b = envelopingAction K n b.val := rfl

/-- The monoid representation underlying the actual compact differential action. -/
def compactEnvelopingRepresentation :
    Representation ℂ (compactEnvelopingSubalgebra K n) (SmoothFunctions K n) :=
  (compactEnvelopingAction K n).toMonoidHom

@[simp]
theorem compactEnvelopingRepresentation_apply (b : compactEnvelopingSubalgebra K n) :
    compactEnvelopingRepresentation K n b = compactEnvelopingAction K n b := rfl

/-- The compact differential orbit span of one smooth function. -/
def compactOrbitSpan (f : SmoothFunctions K n) : Submodule ℂ (SmoothFunctions K n) :=
  Langlands.FiniteVectors.orbitSpan (compactEnvelopingRepresentation K n) f

/-- Finiteness under the compact enveloping subalgebra, without a compact group assertion. -/
def IsCompactLieFinite (f : SmoothFunctions K n) : Prop :=
  Module.Finite ℂ (compactOrbitSpan K n f)

/-- The actual commuting center and compact actions form a product monoid representation. -/
def jointRepresentation :
    Representation ℂ (EnvelopingCenter K n × compactEnvelopingSubalgebra K n)
      (SmoothFunctions K n) where
  toFun p := envelopingAction K n (centerInclusion K n p.1 * p.2.val)
  map_one' := by simp
  map_mul' p q := by
    have h : centerInclusion K n (p.1 * q.1) * (p.2.val * q.2.val) =
        (centerInclusion K n p.1 * p.2.val) *
          (centerInclusion K n q.1 * q.2.val) := by
      rw [map_mul]
      calc
        (centerInclusion K n p.1 * centerInclusion K n q.1) * (p.2.val * q.2.val) =
            centerInclusion K n p.1 * ((centerInclusion K n q.1 * p.2.val) * q.2.val) := by
          simp only [mul_assoc]
        _ = centerInclusion K n p.1 * ((p.2.val * centerInclusion K n q.1) * q.2.val) := by
          rw [centerInclusion_commute K n q.1 p.2.val]
        _ = (centerInclusion K n p.1 * p.2.val) *
            (centerInclusion K n q.1 * q.2.val) := by simp only [mul_assoc]
    exact (congrArg (envelopingAction K n) h).trans
      ((envelopingAction K n).map_mul _ _)

@[simp]
theorem jointRepresentation_apply (z : EnvelopingCenter K n)
    (b : compactEnvelopingSubalgebra K n) (f : SmoothFunctions K n) :
    jointRepresentation K n (z, b) f =
      envelopingAction K n (centerInclusion K n z * b.val) f := rfl

theorem jointRepresentation_apply_eq (z : EnvelopingCenter K n)
    (b : compactEnvelopingSubalgebra K n) (f : SmoothFunctions K n) :
    jointRepresentation K n (z, b) f =
      centerAction K n z (compactEnvelopingAction K n b f) :=
  envelopingAction_mul K n _ _ f

@[simp]
theorem jointRepresentation_center (z : EnvelopingCenter K n) :
    jointRepresentation K n (z, 1) = centerAction K n z := by
  change envelopingAction K n (centerInclusion K n z * 1) = _
  simp

@[simp]
theorem jointRepresentation_compact (b : compactEnvelopingSubalgebra K n) :
    jointRepresentation K n (1, b) = compactEnvelopingAction K n b := by
  change envelopingAction K n (centerInclusion K n 1 * b.val) = _
  simp

/-- The complex span of all actual joint center and compact differential translates. -/
def jointOrbitSpan (f : SmoothFunctions K n) : Submodule ℂ (SmoothFunctions K n) :=
  Langlands.FiniteVectors.orbitSpan (jointRepresentation K n) f

theorem jointAction_mem_jointOrbitSpan (f : SmoothFunctions K n)
    (z : EnvelopingCenter K n) (b : compactEnvelopingSubalgebra K n) :
    envelopingAction K n (centerInclusion K n z * b.val) f ∈ jointOrbitSpan K n f :=
  Langlands.FiniteVectors.action_mem_orbitSpan (jointRepresentation K n) (z, b) f

theorem self_mem_jointOrbitSpan (f : SmoothFunctions K n) :
    f ∈ jointOrbitSpan K n f :=
  Langlands.FiniteVectors.self_mem_orbitSpan (jointRepresentation K n) f

/-- The joint orbit span bundled with its actual invariance. -/
def jointOrbitSubrepresentation (f : SmoothFunctions K n) :
    Subrepresentation (jointRepresentation K n) :=
  Langlands.FiniteVectors.orbitSubrepresentation (jointRepresentation K n) f

theorem jointOrbitSpan_le (f : SmoothFunctions K n)
    (S : Subrepresentation (jointRepresentation K n)) (hf : f ∈ S) :
    jointOrbitSpan K n f ≤ S.toSubmodule :=
  Langlands.FiniteVectors.orbitSpan_le (jointRepresentation K n) f S hf

theorem centerOrbitSpan_le_jointOrbitSpan (f : SmoothFunctions K n) :
    centerOrbitSpan K n f ≤ jointOrbitSpan K n f := by
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  simpa [jointOrbitSpan] using
    Langlands.FiniteVectors.action_mem_orbitSpan (jointRepresentation K n) (z, 1) f

theorem compactOrbitSpan_le_jointOrbitSpan (f : SmoothFunctions K n) :
    compactOrbitSpan K n f ≤ jointOrbitSpan K n f := by
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  simpa [jointOrbitSpan] using
    Langlands.FiniteVectors.action_mem_orbitSpan (jointRepresentation K n) (1, b) f

/-- Finiteness of this function's actual joint orbit, not of the ambient function space. -/
def IsJointFinite (f : SmoothFunctions K n) : Prop :=
  Module.Finite ℂ (jointOrbitSpan K n f)

theorem isJointFinite_iff (f : SmoothFunctions K n) :
    IsJointFinite K n f ↔
      ∃ S : Subrepresentation (jointRepresentation K n),
        Module.Finite ℂ S.toSubmodule ∧ f ∈ S :=
  Langlands.FiniteVectors.isFiniteVector_iff (jointRepresentation K n) f

/-- The actual subspace of smooth functions with finite joint orbit. -/
def jointFiniteFunctions : Submodule ℂ (SmoothFunctions K n) :=
  (Langlands.FiniteVectors.subrepresentation (jointRepresentation K n)).toSubmodule

@[simp]
theorem mem_jointFiniteFunctions (f : SmoothFunctions K n) :
    f ∈ jointFiniteFunctions K n ↔ IsJointFinite K n f := Iff.rfl

theorem isJointFinite_jointAction (f : SmoothFunctions K n)
    (hf : IsJointFinite K n f) (z : EnvelopingCenter K n)
    (b : compactEnvelopingSubalgebra K n) :
    IsJointFinite K n (envelopingAction K n (centerInclusion K n z * b.val) f) :=
  Langlands.FiniteVectors.IsFiniteVector.action hf (z, b)

theorem isJointFinite_centerAction (f : SmoothFunctions K n)
    (hf : IsJointFinite K n f) (z : EnvelopingCenter K n) :
    IsJointFinite K n (centerAction K n z f) := by
  simpa using isJointFinite_jointAction K n f hf z 1

theorem isJointFinite_compactEnvelopingAction (f : SmoothFunctions K n)
    (hf : IsJointFinite K n f) (b : compactEnvelopingSubalgebra K n) :
    IsJointFinite K n (compactEnvelopingAction K n b f) := by
  simpa using isJointFinite_jointAction K n f hf 1 b

theorem isCenterFinite_of_isJointFinite (f : SmoothFunctions K n)
    (hf : IsJointFinite K n f) : IsCenterFinite K n f := by
  have : Module.Finite ℂ (jointOrbitSpan K n f) := hf
  exact Submodule.finiteDimensional_of_le (centerOrbitSpan_le_jointOrbitSpan K n f)

theorem isCompactLieFinite_of_isJointFinite (f : SmoothFunctions K n)
    (hf : IsJointFinite K n f) : IsCompactLieFinite K n f := by
  have : Module.Finite ℂ (jointOrbitSpan K n f) := hf
  exact Submodule.finiteDimensional_of_le (compactOrbitSpan_le_jointOrbitSpan K n f)

end Langlands.Global.ArchimedeanGL
