import Langlands.Algebra.CentralSimple.LandherrNormSemilinear
import Langlands.LinearAlgebra.QuadraticNormLocalGlobal
import Langlands.Global.FiniteCompletionLocalField
import Langlands.Algebra.LocalUnitaryDivisionCommutativeProof
import Langlands.Algebra.CentralSimple.UnitaryDivisionSplitting

/-! # Semilinearity of the relative reduced norm over a number field -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open NumberField IsDedekindDomain
open scoped TensorProduct

universe u

/-- Every finite completion of a number field has the unitary splitting property. -/
theorem finiteCompletion_unitaryInvolutionSplitting {F : Type u} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : UnitaryInvolutionSplitting (v.adicCompletion F) := by
  letI := Global.FiniteCompletion.valuativeRel v
  haveI := Global.FiniteCompletion.isNonarchimedeanLocalField v
  exact Algebra.CentralSimple.unitaryDivisionSplitting _ (localUnitaryDivisionCommutative _)

variable (F E : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

/-- Some finite completion of `F` does not contain a square root of `d`. -/
theorem exists_finitePlace_not_isSquare :
    ∃ v : HeightOneSpectrum (𝓞 F),
      ¬ IsSquare (algebraMap F (v.adicCompletion F) (skewSq F E)) := by
  by_contra h
  push Not at h
  exact not_isSquare_skewSq F E (QuadraticNormLocalGlobal.isSquare_of_all_finite h)

variable (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
  (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))

include hτ in
/-- Over a number field `F`, if `τ` acts on `E` by quadratic conjugation, then the relative
reduced norm satisfies `ν_R(τ_R z) = σ_R(ν_R z)` for every commutative `F`-algebra `R`. -/
theorem relNorm_baseChange (R : Type u) [CommRing R] [Algebra F R] (z : R ⊗[F] B) :
    relNorm F E B R (τ.baseChange R z) = tensorConj F E R (relNorm F E B R z) := by
  obtain ⟨v, hv⟩ := exists_finitePlace_not_isSquare F E
  haveI : Fact (¬ IsSquare (algebraMap F (v.adicCompletion F) (skewSq F E))) := ⟨hv⟩
  exact relNorm_baseChange_of_nonsplit F E B τ hτ (v.adicCompletion F)
    (finiteCompletion_unitaryInvolutionSplitting v) R z

end Langlands.CentralSimple.Landherr
