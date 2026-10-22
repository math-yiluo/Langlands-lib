import Langlands.Global.ArchimedeanEnvelopingAction
import Langlands.Representation.FiniteVectors

/-! # Center orbits of the actual archimedean differential action -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The monoid representation underlying the actual center algebra action. -/
def centerRepresentation : Representation ℂ (EnvelopingCenter K n) (SmoothFunctions K n) :=
  (centerAction K n).toMonoidHom

@[simp]
theorem centerRepresentation_apply (z : EnvelopingCenter K n) :
    centerRepresentation K n z = centerAction K n z := rfl

/-- Evaluation of the actual center action at one smooth function. -/
def centerOrbitMap (f : SmoothFunctions K n) :
    EnvelopingCenter K n →ₗ[ℂ] SmoothFunctions K n where
  toFun z := centerAction K n z f
  map_add' z w := by simp
  map_smul' c z := by simp

@[simp]
theorem centerOrbitMap_apply (f : SmoothFunctions K n) (z : EnvelopingCenter K n) :
    centerOrbitMap K n f z = centerAction K n z f := rfl

/-- The complex span of the orbit under the actual enveloping-algebra center. -/
def centerOrbitSpan (f : SmoothFunctions K n) : Submodule ℂ (SmoothFunctions K n) :=
  Langlands.FiniteVectors.orbitSpan (centerRepresentation K n) f

theorem centerOrbitSpan_eq_range (f : SmoothFunctions K n) :
    centerOrbitSpan K n f = LinearMap.range (centerOrbitMap K n f) := by
  change Submodule.span ℂ (Set.range (centerOrbitMap K n f)) = _
  exact Submodule.span_eq (LinearMap.range (centerOrbitMap K n f))

theorem centerAction_mem_centerOrbitSpan (f : SmoothFunctions K n)
    (z : EnvelopingCenter K n) : centerAction K n z f ∈ centerOrbitSpan K n f :=
  Langlands.FiniteVectors.action_mem_orbitSpan (centerRepresentation K n) z f

theorem self_mem_centerOrbitSpan (f : SmoothFunctions K n) :
    f ∈ centerOrbitSpan K n f :=
  Langlands.FiniteVectors.self_mem_orbitSpan (centerRepresentation K n) f

/-- A finiteness condition on one function's center orbit, not on all smooth functions. -/
def IsCenterFinite (f : SmoothFunctions K n) : Prop :=
  Module.Finite ℂ (centerOrbitSpan K n f)

/-- The actual complex subspace of center-finite smooth functions. -/
def centerFiniteFunctions : Submodule ℂ (SmoothFunctions K n) :=
  (Langlands.FiniteVectors.subrepresentation (centerRepresentation K n)).toSubmodule

@[simp]
theorem mem_centerFiniteFunctions (f : SmoothFunctions K n) :
    f ∈ centerFiniteFunctions K n ↔ IsCenterFinite K n f := Iff.rfl

theorem isCenterFinite_centerAction (f : SmoothFunctions K n)
    (hf : IsCenterFinite K n f) (z : EnvelopingCenter K n) :
    IsCenterFinite K n (centerAction K n z f) :=
  Langlands.FiniteVectors.IsFiniteVector.action hf z

end Langlands.Global.ArchimedeanGL
