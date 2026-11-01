import Langlands.Global.FiniteAdelicGL.TensorTransportFormulas
import Langlands.Automorphic.FiniteTensorCMTransport

/-! # Finite-stage formulas for genuine CM tensor presentations -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor
open AdelicFunctoriality

variable {F : Type uF} [Field F] [NumberField F] [NumberField.IsCMField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorCMFormulaRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorCMFormulaContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorCMFormulaSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorCMFormulaFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}

/-- The CM image of a finite stage, with the exact original exceptions. -/
def complexConjTensorIndex (T : Index (complexConjExceptional (E := E))) : Index E :=
  transportTensorIndex (CMConjugation.fieldConj F) E T

variable (P : FiniteTensorPresentation F n ρ E e he S)

/-- Rebasing the action does not change the actual finite-stage reindexing map. -/
theorem complexConjTensorEquiv_of
    (T : Index (complexConjExceptional (E := E)))
    (x : Stage ℂ (fun v => V (finitePlaceEquiv (CMConjugation.fieldConj F) v)) T.1) :
    P.complexConjTensorEquiv
      (of ℂ (fun v => V (finitePlaceEquiv (CMConjugation.fieldConj F) v))
        (complexConjExceptional (E := E))
        (fun v => e (finitePlaceEquiv (CMConjugation.fieldConj F) v)) T x) =
      of ℂ V E e (complexConjTensorIndex T)
        (reindexStage (finitePlaceEquiv (CMConjugation.fieldConj F)) T.1 x) :=
  tensorTransportEquiv_of (CMConjugation.fieldConj F) ρ E e he P.reference_nonzero T x

/-- The finite-stage presentation is followed by the actual CM function image map. -/
theorem complexConjEquiv_of
    (T : Index (complexConjExceptional (E := E)))
    (x : Stage ℂ (fun v => V (finitePlaceEquiv (CMConjugation.fieldConj F) v)) T.1) :
    P.complexConjEquiv
      (of ℂ (fun v => V (finitePlaceEquiv (CMConjugation.fieldConj F) v))
        (complexConjExceptional (E := E))
        (fun v => e (finitePlaceEquiv (CMConjugation.fieldConj F) v)) T x) =
      S.complexConjEquiv
        (P.equiv (of ℂ V E e (complexConjTensorIndex T)
          (reindexStage (finitePlaceEquiv (CMConjugation.fieldConj F)) T.1 x))) := by
  exact congrArg (fun y : Space ℂ V E e => S.complexConjEquiv (P.equiv y))
    (P.complexConjTensorEquiv_of T x)

/-- Evaluation of an arbitrary finite-stage vector pulls back the adelic argument. -/
theorem evaluate_complexConjEquiv_of
    (T : Index (complexConjExceptional (E := E)))
    (x : Stage ℂ (fun v => V (finitePlaceEquiv (CMConjugation.fieldConj F) v)) T.1)
    (a : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
      (S.complexConj.toContinuous (P.complexConjEquiv
        (of ℂ (fun v => V (finitePlaceEquiv (CMConjugation.fieldConj F) v))
          (complexConjExceptional (E := E))
          (fun v => e (finitePlaceEquiv (CMConjugation.fieldConj F) v)) T x))) a =
      ContinuousRationalFunctions.evaluate F n
        (S.toContinuous (P.equiv (of ℂ V E e (complexConjTensorIndex T)
          (reindexStage (finitePlaceEquiv (CMConjugation.fieldConj F)) T.1 x))))
        (CMConjugation.adelicConj F n a) := by
  rw [evaluate_complexConjEquiv, complexConjTensorEquiv_of]

/-- On elementary tensors the entries are pulled back along the actual place map. -/
theorem complexConjTensorEquiv_pure
    (T : Index (complexConjExceptional (E := E)))
    (x : ∀ v : T.1.map (finitePlaceEquiv (CMConjugation.fieldConj F)).toEmbedding,
      V v) :
    P.complexConjTensorEquiv
      (pure (complexConjExceptional (E := E))
        (fun v => e (finitePlaceEquiv (CMConjugation.fieldConj F) v)) T
        (fun v => x (reindexFinite (finitePlaceEquiv (CMConjugation.fieldConj F))
          T.1 v))) =
      pure E e (complexConjTensorIndex T) x :=
  tensorTransportEquiv_pure (CMConjugation.fieldConj F) ρ E e he P.reference_nonzero T x

/-- Elementary tensor presentation into the specified actual CM image. -/
theorem complexConjEquiv_pure
    (T : Index (complexConjExceptional (E := E)))
    (x : ∀ v : T.1.map (finitePlaceEquiv (CMConjugation.fieldConj F)).toEmbedding,
      V v) :
    P.complexConjEquiv
      (pure (complexConjExceptional (E := E))
        (fun v => e (finitePlaceEquiv (CMConjugation.fieldConj F) v)) T
        (fun v => x (reindexFinite (finitePlaceEquiv (CMConjugation.fieldConj F))
          T.1 v))) =
      S.complexConjEquiv (P.equiv (pure E e (complexConjTensorIndex T) x)) := by
  exact congrArg (fun y : Space ℂ V E e => S.complexConjEquiv (P.equiv y))
    (P.complexConjTensorEquiv_pure T x)

/-- The bundled genuine CM presentation evaluates elementary tensors by argument
pullback, with the original presentation on the actual image stage. -/
theorem evaluate_complexConj_pure
    (T : Index (complexConjExceptional (E := E)))
    (x : ∀ v : T.1.map (finitePlaceEquiv (CMConjugation.fieldConj F)).toEmbedding,
      V v) (a : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
      (S.complexConj.toContinuous ((P.complexConj).equiv
        (pure (complexConjExceptional (E := E))
          (fun v => e (finitePlaceEquiv (CMConjugation.fieldConj F) v)) T
          (fun v => x (reindexFinite (finitePlaceEquiv (CMConjugation.fieldConj F))
            T.1 v))))) a =
      ContinuousRationalFunctions.evaluate F n
        (S.toContinuous (P.equiv (pure E e (complexConjTensorIndex T) x)))
        (CMConjugation.adelicConj F n a) := by
  change ContinuousRationalFunctions.evaluate F n
    (S.complexConj.toContinuous (P.complexConjEquiv _)) a = _
  rw [evaluate_complexConjEquiv, complexConjTensorEquiv_pure]

end FiniteTensorPresentation
end Langlands.Automorphic
