import Langlands.Weil.Local.Parameters
import Langlands.WeilDeligne.ParameterOperations
import Langlands.WeilDeligne.Invariants

/-! # Constructions on actual local Weil–Deligne parameters -/

noncomputable section

universe u v w

namespace Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The actual norm is trivial on actual inertia, as required by block and invariant constructors. -/
theorem localNormCharacter_on_inertia (i : localInertia F) :
    localNormCharacter F i = 1 :=
  residueNormCharacter_on_kernel F.canonicalTopologicalData (localDegree F) i.property

/-- Sum on the constructed local group, with the inherited open inertia certificate. -/
def localParameterSum (A : LocalParameterObjects.{u, v} F)
    (B : LocalParameterObjects.{u, w} F) : LocalParameterObjects.{u, max v w} F :=
  WeilDeligneRepresentation.parameterSum (localInertia F) A B

/-- Tensor with monodromy `N tensor 1 + 1 tensor N'`. -/
def localParameterTensor (A : LocalParameterObjects.{u, v} F)
    (B : LocalParameterObjects.{u, w} F) : LocalParameterObjects.{u, max v w} F :=
  WeilDeligneRepresentation.parameterTensor (localInertia F) A B

/-- Full linear dual with negative-transpose monodromy. -/
def localParameterDual (A : LocalParameterObjects.{u, v} F) :
    LocalParameterObjects.{u, v} F :=
  WeilDeligneRepresentation.parameterDual (localInertia F) A

/-- Character twist with its necessary explicit open inertia-kernel condition. -/
def localParameterTwist (χ : localWeilGroup F →* ℂˣ)
    (hχ : IsOpen ((χ.comp (localInertia F).subtype).ker : Set (localInertia F)))
    (A : LocalParameterObjects.{u, v} F) : LocalParameterObjects.{u, v} F :=
  WeilDeligneRepresentation.parameterTwist (localInertia F) χ hχ A

/-- The constructed unramified character has open kernel on actual inertia. -/
theorem localUnramifiedCharacter_inertiaKernel_isOpen (z : ℂˣ) :
    IsOpen (((localUnramifiedCharacter F z).toMonoidHom.comp
      (localInertia F).subtype).ker : Set (localInertia F)) := by
  have h : ((localUnramifiedCharacter F z).toMonoidHom.comp
      (localInertia F).subtype).ker = ⊤ := by
    apply top_unique
    intro i _
    exact unramifiedCharacter_on_kernel (localDegree F) z i.property
  rw [h]
  exact isOpen_univ

/-- Twisting by the actual unramified character requires no additional kernel hypothesis. -/
def localParameterUnramifiedTwist (z : ℂˣ) (A : LocalParameterObjects.{u, v} F) :
    LocalParameterObjects.{u, v} F :=
  localParameterTwist F (localUnramifiedCharacter F z).toMonoidHom
    (localUnramifiedCharacter_inertiaKernel_isOpen F z) A

/-- Determinant gives the scalar parameter with zero monodromy. -/
def localParameterDeterminant (A : LocalParameterObjects.{u, v} F) :
    LocalParameterObjects.{u, 0} F :=
  WeilDeligneRepresentation.parameterDeterminant (localInertia F) A

/-- The Weil representation on the actual monodromy kernel. -/
def localParameterKernel (A : LocalParameterObjects.{u, v} F) :
    LocalOpenInertiaWeilObjects.{u, v} F :=
  WeilDeligneRepresentation.parameterKernel (localInertia F) A

/-- The Weil representation on `(ker N)^I` for actual local inertia. -/
def localParameterInertiaKernel (A : LocalParameterObjects.{u, v} F) :
    LocalOpenInertiaWeilObjects.{u, v} F :=
  WeilDeligneRepresentation.parameterInertiaKernel (localInertia F) A

/-- The pair on `V^I`, retaining the restriction of possibly nonzero monodromy. -/
def localParameterInvariants (A : LocalParameterObjects.{u, v} F) :
    LocalParameterObjects.{u, v} F :=
  WeilDeligneRepresentation.parameterInvariants (localInertia F)
    (localNormCharacter_on_inertia F) (localInertia F) A

/-- The actual uncentered special block, with no assumed norm-triviality certificate. -/
def localSpecialBlock (m : ℕ) : LocalParameterObjects.{u, 0} F :=
  WeilDeligneRepresentation.specialBlockParameter (localInertia F)
    (localNormCharacter F).toMonoidHom (localNormCharacter_on_inertia F) m

/-- The actual block has its advertised rank, including the internal zero block. -/
theorem localSpecialBlock_rank (m : ℕ) : (localSpecialBlock F m).val.rank = m :=
  WeilDeligneRepresentation.rank_specialBlock (localNormCharacter F).toMonoidHom m

/-- In positive rank, the monodromy kernel is the top-weight line. -/
theorem localSpecialBlock_kernel (n : ℕ) :
    LinearMap.ker (localSpecialBlock F (n + 1)).val.monodromy =
      Submodule.span ℂ {WeilDeligneRepresentation.Special.topVector ℂ n} :=
  WeilDeligneRepresentation.ker_specialBlock (localNormCharacter F).toMonoidHom n

/-- The actual local parameter space contains blocks with genuinely nonzero monodromy. -/
theorem localSpecialBlock_monodromy_ne_zero (n : ℕ) :
    (localSpecialBlock F (n + 2)).val.monodromy ≠ 0 :=
  WeilDeligneRepresentation.specialBlock_monodromy_ne_zero
    (localNormCharacter F).toMonoidHom n

/-- Form the specified block from an actual open-inertia Weil factor. -/
def localBlock (A : LocalOpenInertiaWeilObjects.{u, v} F) (m : ℕ) :
    LocalParameterObjects.{u, v} F :=
  WeilDeligneRepresentation.blockParameter (localInertia F)
    (localNormCharacter F).toMonoidHom (localNormCharacter_on_inertia F) A m

/-- Sum on genuine local parameter classes. -/
abbrev localParameterSumClass :
    LocalParameterClasses.{u, v} F → LocalParameterClasses.{u, w} F →
      LocalParameterClasses.{u, max v w} F :=
  WeilDeligneRepresentation.parameterSumClass (localInertia F)

/-- Tensor on genuine local parameter classes. -/
abbrev localParameterTensorClass :
    LocalParameterClasses.{u, v} F → LocalParameterClasses.{u, w} F →
      LocalParameterClasses.{u, max v w} F :=
  WeilDeligneRepresentation.parameterTensorClass (localInertia F)

/-- Duality on genuine local parameter classes. -/
abbrev localParameterDualClass :
    LocalParameterClasses.{u, v} F → LocalParameterClasses.{u, v} F :=
  WeilDeligneRepresentation.parameterDualClass (localInertia F)

/-- An allowed character twist on genuine local parameter classes. -/
abbrev localParameterTwistClass (χ : localWeilGroup F →* ℂˣ)
    (hχ : IsOpen ((χ.comp (localInertia F).subtype).ker : Set (localInertia F))) :
    LocalParameterClasses.{u, v} F → LocalParameterClasses.{u, v} F :=
  WeilDeligneRepresentation.parameterTwistClass (localInertia F) χ hχ

/-- Twisting genuine local parameter classes by the actual unramified character. -/
abbrev localParameterUnramifiedTwistClass (z : ℂˣ) :
    LocalParameterClasses.{u, v} F → LocalParameterClasses.{u, v} F :=
  localParameterTwistClass F (localUnramifiedCharacter F z).toMonoidHom
    (localUnramifiedCharacter_inertiaKernel_isOpen F z)

/-- Determinant on genuine local parameter classes. -/
abbrev localParameterDeterminantClass :
    LocalParameterClasses.{u, v} F → LocalParameterClasses.{u, 0} F :=
  WeilDeligneRepresentation.parameterDeterminantClass (localInertia F)

/-- Monodromy kernels on genuine local parameter classes, as open-inertia Weil classes. -/
abbrev localParameterKernelClass :
    LocalParameterClasses.{u, v} F →
      FiniteRepresentation.IsomorphismClassesWith
        (fun A : LocalWeilRepresentation.{u, v} F => A.HasOpenInertiaKernel (localInertia F)) :=
  WeilDeligneRepresentation.parameterKernelClass (localInertia F)

/-- Inertia-fixed monodromy kernels on genuine local parameter classes. -/
abbrev localParameterInertiaKernelClass :
    LocalParameterClasses.{u, v} F →
      FiniteRepresentation.IsomorphismClassesWith
        (fun A : LocalWeilRepresentation.{u, v} F => A.HasOpenInertiaKernel (localInertia F)) :=
  WeilDeligneRepresentation.parameterInertiaKernelClass (localInertia F)

/-- Invariant pairs on genuine local parameter classes. -/
abbrev localParameterInvariantsClass :
    LocalParameterClasses.{u, v} F → LocalParameterClasses.{u, v} F :=
  WeilDeligneRepresentation.parameterInvariantsClass (localInertia F)
    (localNormCharacter_on_inertia F) (localInertia F)

end Langlands.Weil.Local
