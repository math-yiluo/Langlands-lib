import Langlands.WeilDeligne.Parameters
import Langlands.WeilDeligne.Dual
import Langlands.WeilDeligne.Twist
import Langlands.WeilDeligne.Determinant
import Langlands.WeilDeligne.Kernels
import Langlands.WeilDeligne.SpecialBlocks
import Langlands.Weil.Representation.InertiaOperations

/-! # Actual algebraic parameter operations with proved inertia certificates -/

noncomputable section

universe uG uV uW

namespace Langlands.WeilDeligneRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ν : G →* ℂˣ} (I : Subgroup G)

/-- Sum of parameters, including its open inertia certificate. -/
def parameterSum (A : ParameterObjects.{uG, uV} (ν := ν) I)
    (B : ParameterObjects.{uG, uW} (ν := ν) I) :
    ParameterObjects.{uG, max uV uW} (ν := ν) I :=
  ⟨sum A.val B.val,
    FiniteRepresentation.hasOpenInertiaKernel_sum I A.property B.property⟩

/-- Tensor of parameters with the actual tensor monodromy and its inertia certificate. -/
def parameterTensor (A : ParameterObjects.{uG, uV} (ν := ν) I)
    (B : ParameterObjects.{uG, uW} (ν := ν) I) :
    ParameterObjects.{uG, max uV uW} (ν := ν) I :=
  ⟨tensor A.val B.val,
    FiniteRepresentation.hasOpenInertiaKernel_tensor I A.property B.property⟩

/-- Full algebraic dual of a parameter with negative-transpose monodromy. -/
def parameterDual (A : ParameterObjects.{uG, uV} (ν := ν) I) :
    ParameterObjects.{uG, uV} (ν := ν) I :=
  ⟨dual A.val, FiniteRepresentation.hasOpenInertiaKernel_dual I A.property⟩

/-- Twist a parameter by a character whose kernel on inertia is explicitly open. -/
def parameterTwist (χ : G →* ℂˣ) (hχ : IsOpen ((χ.comp I.subtype).ker : Set I))
    (A : ParameterObjects.{uG, uV} (ν := ν) I) : ParameterObjects.{uG, uV} (ν := ν) I :=
  ⟨twist χ A.val, FiniteRepresentation.hasOpenInertiaKernel_twist I χ hχ A.property⟩

/-- The scalar determinant parameter has zero monodromy and an open inertia kernel. -/
def parameterDeterminant (A : ParameterObjects.{uG, uV} (ν := ν) I) :
    ParameterObjects.{uG, 0} (ν := ν) I :=
  ⟨determinant A.val, FiniteRepresentation.hasOpenInertiaKernel_determinant I A.property⟩

/-- The actual monodromy kernel is an open-inertia Weil representation. -/
def parameterKernel (A : ParameterObjects.{uG, uV} (ν := ν) I) :
    FiniteRepresentation.OpenInertiaObjects.{uG, uV} I :=
  ⟨kernelRepresentation A.val,
    FiniteRepresentation.hasOpenInertiaKernel_of_injective I (kernelInclusion A.val)
      Subtype.val_injective A.property⟩

/-- The actual inertia-fixed monodromy kernel, with its open inertia certificate. -/
def parameterInertiaKernel [I.Normal] (A : ParameterObjects.{uG, uV} (ν := ν) I) :
    FiniteRepresentation.OpenInertiaObjects.{uG, uV} I :=
  FiniteRepresentation.openInertiaInvariants I I (parameterKernel I A)

/-- Actual special-block parameters when the supplied norm character is trivial on inertia. -/
def specialBlockParameter (ν : G →* ℂˣ) (hν : ∀ i : I, ν (i : G) = 1) (m : ℕ) :
    ParameterObjects.{uG, 0} (ν := ν) I := by
  refine ⟨specialBlock ν m, ?_⟩
  have hker : (specialBlock ν m).toFiniteRepresentation.inertiaKernel I = ⊤ := by
    apply top_unique
    intro i _
    change Special.action ν m (i : G) = 1
    apply LinearMap.ext
    intro v
    funext j
    change (ν (i : G) : ℂ) ^ j.val * v j = v j
    simp [hν i]
  change IsOpen ((specialBlock ν m).toFiniteRepresentation.inertiaKernel I : Set I)
  rw [hker]
  exact isOpen_univ

/-- The specified block: an open-inertia Weil factor with zero monodromy, tensored with the
special-block parameter, when the norm is trivial on inertia. -/
def blockParameter (ν : G →* ℂˣ) (hν : ∀ i : I, ν (i : G) = 1)
    (A : FiniteRepresentation.OpenInertiaObjects.{uG, uV} I) (m : ℕ) :
    ParameterObjects.{uG, uV} (ν := ν) I :=
  parameterTensor I (zeroMonodromyParameter I ν A.val A.property)
    (specialBlockParameter I ν hν m)

/-- Sum descends to genuine parameter classes. -/
def parameterSumClass :
    ParameterClasses.{uG, uV} (ν := ν) I → ParameterClasses.{uG, uW} (ν := ν) I →
      ParameterClasses.{uG, max uV uW} (ν := ν) I :=
  Quotient.map₂ (parameterSum I) (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨sumEquiv e f⟩)

/-- Tensor descends to genuine parameter classes. -/
def parameterTensorClass :
    ParameterClasses.{uG, uV} (ν := ν) I → ParameterClasses.{uG, uW} (ν := ν) I →
      ParameterClasses.{uG, max uV uW} (ν := ν) I :=
  Quotient.map₂ (parameterTensor I) (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨tensorEquiv e f⟩)

/-- Duality descends to genuine parameter classes. -/
def parameterDualClass : ParameterClasses.{uG, uV} (ν := ν) I →
    ParameterClasses.{uG, uV} (ν := ν) I :=
  Quotient.map (parameterDual I) (fun _ _ ⟨e⟩ => ⟨(dualEquiv e).symm⟩)

/-- An allowed character twist descends to genuine parameter classes. -/
def parameterTwistClass (χ : G →* ℂˣ) (hχ : IsOpen ((χ.comp I.subtype).ker : Set I)) :
    ParameterClasses.{uG, uV} (ν := ν) I → ParameterClasses.{uG, uV} (ν := ν) I :=
  Quotient.map (parameterTwist I χ hχ) (fun _ _ ⟨e⟩ => ⟨twistEquiv χ e⟩)

/-- Determinant descends to genuine parameter classes. -/
def parameterDeterminantClass : ParameterClasses.{uG, uV} (ν := ν) I →
    ParameterClasses.{uG, 0} (ν := ν) I :=
  Quotient.map (parameterDeterminant I) (fun _ _ ⟨e⟩ => ⟨determinantEquiv e⟩)

/-- The monodromy-kernel construction descends to genuine open-inertia Weil classes. -/
def parameterKernelClass : ParameterClasses.{uG, uV} (ν := ν) I →
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.HasOpenInertiaKernel I) :=
  Quotient.map (parameterKernel I) (fun _ _ ⟨e⟩ => ⟨kernelEquiv e⟩)

/-- Inertia-fixed monodromy kernels descend to genuine open-inertia Weil classes. -/
def parameterInertiaKernelClass [I.Normal] :
    ParameterClasses.{uG, uV} (ν := ν) I →
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.HasOpenInertiaKernel I) :=
  Quotient.map (parameterInertiaKernel I)
    (fun _ _ ⟨e⟩ => ⟨FiniteRepresentation.invariantsEquiv I (kernelEquiv e)⟩)

end Langlands.WeilDeligneRepresentation
