import Langlands.Automorphic.FiniteTensorHilbertInvariantRange
import Langlands.Global.FiniteAdelicGL.CompactOpenRefinement
import Langlands.Representation.MatrixCoefficient.HilbertComponentProof

/-! # Admissible local factors in actual tensor Hilbert slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertComponentRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertComponentContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertComponentSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertComponentFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertComponentFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertComponentLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The specified factor completion intertwines the original global completed
representation restricted at the actual local inclusion. -/
def factorHilbertIntertwiner (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    (P.factorUnitaryForm b v y hy).completedRepresentation.IntertwiningMap
      (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom) where
  toLinearMap := (P.factorHilbertEmbedding b v y hy).toLinearMap
  isIntertwining' g := LinearMap.ext (P.factorHilbertEmbedding_completedOperator b v y hy g)

/-- Map original factor vectors into the same global Hilbert completion. -/
def factorHilbertAlgebraicIntertwiner (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :=
  (P.factorHilbertIntertwiner b v y hy).comp
    (CoefficientHilbertComponentAux.toHilbertIntertwiner (P.factorUnitaryForm b v y hy))

/-- An admissible irreducible factor gives a closed-irreducible actual slice
for its inherited local action. -/
theorem sliceHilbertRange_closed_irreducible (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hρ : IsAdmissible (ρ v)) (hI : Representation.IsIrreducible (ρ v)) :
    Nontrivial (P.sliceHilbertRange b v y).toSubmodule ∧
      ∀ T : Subrepresentation (P.sliceHilbertRange b v y).toRepresentation,
        IsClosed (T : Set (P.sliceHilbertRange b v y).toSubmodule) → T = ⊥ ∨ T = ⊤ :=
  CoefficientHilbertComponentAux.closed_irreducible_range
    (σ := (P.factorUnitaryForm b v y hy).completedRepresentation)
    (τ := b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)
    (P.factorHilbertEmbedding b v y hy)
    (fun g x => Representation.IntertwiningMap.isIntertwining _ _
      (P.factorHilbertIntertwiner b v y hy) g x)
    (P.sliceHilbertRange b v y)
    (P.range_factorHilbertEmbedding_eq_sliceHilbertRange b v y hy)
    (CoefficientHilbertComponentAux.completion_closed_irreducible
      (compactOpen_cofinal F n v) hρ hI (P.factorUnitaryForm b v y hy))

/-- The original factor image is exactly the locally smooth part of the
actual completed slice. Smoothness concerns the inserted local group. -/
theorem mem_sliceHilbertRange_and_smooth_iff (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hρ : IsAdmissible (ρ v)) (z : b.HilbertCompletion) :
    (z ∈ P.sliceHilbertRange b v y ∧
      z ∈ smoothVectors (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)) ↔
      ∃ x : V v, P.factorHilbertAlgebraicIntertwiner b v y hy x = z :=
  CoefficientHilbertComponentAux.smooth_range_image
    (σ := (P.factorUnitaryForm b v y hy).completedRepresentation)
    (τ := b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)
    (CoefficientHilbertComponentAux.toHilbertIntertwiner (P.factorUnitaryForm b v y hy))
    (CoefficientHilbertComponentAux.completion_smooth_recovery
      (compactOpen_cofinal F n v) hρ (P.factorUnitaryForm b v y hy))
    (P.factorHilbertEmbedding b v y hy)
    (fun g x => Representation.IntertwiningMap.isIntertwining _ _
      (P.factorHilbertIntertwiner b v y hy) g x)
    (P.sliceHilbertRange b v y)
    (P.range_factorHilbertEmbedding_eq_sliceHilbertRange b v y hy) z

end FiniteTensorPresentation
end Langlands.Automorphic
