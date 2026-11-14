import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.Representation.Induction.BlockFactors

/-!
# All-field port of `Langlands.Representation.Induction.BlockFactors`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.BlockFactors` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped NNReal
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF uV uW uX

section Tensor
variable {F : Type uF} [CommRing F]
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

end Tensor
variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  {X : Fin B.length → Type uX}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uV uW uX

variable {F : LocalFieldPackage.{uF}}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  {X : Fin B.length → Type uX}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- Henniart's `i(σ_1, …, σ_r)` for an actual p-adic field: normalized parabolic
induction, from the standard upper block parabolic with the successive block
sizes, of the tensor product of the block representations. -/
def normalizedProductInduced
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))) :=
  T.normalizedParabolicInduced B (B.blockTensor σ)

theorem isSmooth_normalizedProductInduced
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedProductInduced B σ) :=
  T.isSmooth_normalizedParabolicInduced B (B.blockTensor σ)

/-- The induced map of a family of actual block intertwiners. -/
def normalizedProductInducedMap
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i)}
    (f : ∀ i, (σ i).IntertwiningMap (τ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).IntertwiningMap (T.normalizedProductInduced B τ) :=
  T.normalizedParabolicInducedMap B (FiniteTensor.externalMap f)

/-- `i(σ_1, …, σ_r)` as a functor from families of smooth block representations
to smooth representations of `GL_n(F)`. -/
def normalizedProductInductionFunctor :
    letI := T.topology
    (∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.productInductionFunctorOf (T.leviHalfCharacter B)

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe uF uV

variable (F : LocalFieldPackage.{uF})
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

end Langlands.AllFieldBZ.LocalFieldPackage
