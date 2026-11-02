import Langlands.Automorphic.FiniteTensorHilbertRange
import Langlands.Representation.Unitary.CompletionRestrictionIntertwiner

/-! # Covariance of actual automorphic tensor Hilbert maps -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertCovarianceRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertCovarianceContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertCovarianceSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertCovarianceFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertCovarianceFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertCovarianceLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The separated completion intertwines the actual local insertion into the
original global completed representation. -/
theorem separatedHilbertEquiv_completedOperator (v : FinitePlace F)
    (g : FiniteLocalGL F n v) (x : (P.separatedUnitaryForm b v).HilbertCompletion) :
    P.separatedHilbertEquiv b v ((P.separatedUnitaryForm b v).completedOperator g x) =
      b.completedOperator (localInclusion F n v g) (P.separatedHilbertEquiv b v x) :=
  (P.separatedUnitaryForm b v).completedEquiv_comp_completedOperator b
    (localInclusion F n v).toMonoidHom (P.localEquiv v).toIntertwiningMap
    (fun _ _ => rfl) (P.localEquiv v).surjective g x

/-- The completed slice inclusion intertwines the local completed action with
its actual insertion into the original global completed action. -/
theorem sliceHilbertEmbedding_completedOperator (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (g : FiniteLocalGL F n v)
    (x : (P.sliceUnitaryForm b v y).HilbertCompletion) :
    P.sliceHilbertEmbedding b v y ((P.sliceUnitaryForm b v y).completedOperator g x) =
      b.completedOperator (localInclusion F n v g) (P.sliceHilbertEmbedding b v y x) :=
  (P.sliceUnitaryForm b v y).completedIsometry_comp_completedOperator b
    (localInclusion F n v).toMonoidHom (P.sliceInclusion v y) (fun _ _ => rfl) g x

/-- The completed factor-to-slice equivalence intertwines the two actual
local completed actions. -/
theorem factorSliceHilbertEquiv_completedOperator (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (g : FiniteLocalGL F n v) (x : (P.factorUnitaryForm b v y hy).HilbertCompletion) :
    P.factorSliceHilbertEquiv b v y hy
        ((P.factorUnitaryForm b v y hy).completedOperator g x) =
      (P.sliceUnitaryForm b v y).completedOperator g
        (P.factorSliceHilbertEquiv b v y hy x) :=
  (P.factorUnitaryForm b v y hy).completedEquiv_completedOperator
    (P.sliceUnitaryForm b v y) (P.sliceEquiv v y hy).toIntertwiningMap
    (fun _ _ => rfl) (P.sliceEquiv v y hy).surjective g x

/-- The specified factor's completed action agrees with the original global
action on its completed fixed-tail image. -/
theorem factorHilbertEmbedding_completedOperator (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (g : FiniteLocalGL F n v) (x : (P.factorUnitaryForm b v y hy).HilbertCompletion) :
    P.factorHilbertEmbedding b v y hy
        ((P.factorUnitaryForm b v y hy).completedOperator g x) =
      b.completedOperator (localInclusion F n v g) (P.factorHilbertEmbedding b v y hy x) := by
  change P.sliceHilbertEmbedding b v y
    (P.factorSliceHilbertEquiv b v y hy
      ((P.factorUnitaryForm b v y hy).completedOperator g x)) = _
  exact (congrArg (P.sliceHilbertEmbedding b v y)
    (P.factorSliceHilbertEquiv_completedOperator b v y hy g x)).trans
      (P.sliceHilbertEmbedding_completedOperator b v y g
        (P.factorSliceHilbertEquiv b v y hy x))

/-- The actual completed slice inclusion as an intertwiner into the restriction
of the original global completed representation. -/
def sliceHilbertIntertwiner (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    (P.sliceUnitaryForm b v y).completedRepresentation.IntertwiningMap
      (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom) where
  toLinearMap := (P.sliceHilbertEmbedding b v y).toLinearMap
  isIntertwining' g := LinearMap.ext (P.sliceHilbertEmbedding_completedOperator b v y g)

theorem sliceHilbertIntertwiner_apply (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (x : (P.sliceUnitaryForm b v y).HilbertCompletion) :
    P.sliceHilbertIntertwiner b v y x = P.sliceHilbertEmbedding b v y x := rfl

end FiniteTensorPresentation
end Langlands.Automorphic
