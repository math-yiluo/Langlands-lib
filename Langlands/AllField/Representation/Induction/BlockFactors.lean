import Langlands.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.Induction.Parabolic
/-!
# Normalized induction of block factors

For representations `σ_1, …, σ_r` of the diagonal blocks `GL_{n_i}`, the actual
block Levi acts on their external tensor product, and normalized parabolic
induction from the standard upper block parabolic gives the representation
`i(σ_1, …, σ_r)` of `GL_n`.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW uX

section Tensor


end Tensor


end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV uW uX

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  {X : Fin B.length → Type uX}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- Henniart's `i(σ_1, …, σ_r)` for an actual p-adic field: normalized parabolic
induction, from the standard upper block parabolic with the successive block
sizes, of the tensor product of the block representations. -/
def normalizedProductInduced
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F)
      (Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F)))) :=
  T.normalizedParabolicInduced B (B.blockTensor σ)

/-- The covariance `f (p g) = δ_P(m)^(1/2) (σ_1(m_1) ⊗ ⋯ ⊗ σ_r(m_r)) (f g)`,
with `m = (m_1, …, m_r)` the Levi part of `p`. -/
theorem normalizedProductInduced_covariant
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F))))
    (g : B.parabolic F) (x : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F)))
        f ((g : GeneralLinear n F) * x) =
      ((NNReal.sqrt (T.leviModulus B (B.leviProjection F g) : ℝ≥0) : ℝ) : ℂ) •
        B.blockTensor σ (B.leviProjection F g)
          (Induction.eval (B.parabolic F)
            (twist (T.parabolicHalfModulus B)
              ((B.blockTensor σ).comp (B.leviProjection F))) f x) :=
  T.normalizedParabolicInduced_covariant B (B.blockTensor σ) f g x

theorem isSmooth_normalizedProductInduced
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedProductInduced B σ) :=
  T.isSmooth_normalizedParabolicInduced B (B.blockTensor σ)

/-- The induced map of a family of actual block intertwiners. -/
def normalizedProductInducedMap
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)}
    (f : ∀ i, (σ i).IntertwiningMap (τ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).IntertwiningMap (T.normalizedProductInduced B τ) :=
  T.normalizedParabolicInducedMap B (FiniteTensor.externalMap f)

/-- `i(σ_1, …, σ_r)` as a functor from families of smooth block representations
to smooth representations of `GL_n(F)`. -/
def normalizedProductInductionFunctor :
    letI := T.topology
    (∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.productInductionFunctorOf (T.leviHalfCharacter B)

end Langlands.LocalFieldData

namespace Langlands

universe uF uV


end Langlands
