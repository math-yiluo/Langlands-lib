import Langlands.LocalFactor.NonabelianDualityStatement
import Langlands.LocalFactor.NonabelianUniquenessStatement

/-!
# The multiplicative defect of fixed-Haar duality

The defect is a homomorphism on the actual continuous exact virtual group.
The reduction to induced character differences retains the generation premise
and the equations on those generators explicitly.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The product in the fixed-Haar equation, regarded as an additive
homomorphism with values in the additive notation for the complex units.
Only the system's additivity law is needed for this construction. -/
def dualityDefect (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E) :
    Virtual.{uF, uV} F E →+ Additive ℂˣ := by
  letI := (fieldData F E).topology
  letI := (fieldData F E).valuativeRel
  letI := (fieldData F E).localField
  let T : Virtual.{uF, uV} F E →ₗ[ℤ] Virtual.{uF, uV} F E :=
    (ExactGrothendieckGroup.continuousTwist
      (CommonClosureWeilDeligne.normCharacter F E)).toLinearMap.comp
      ExactGrothendieckGroup.continuousDual.toLinearMap
  exact {
    toFun x := Additive.ofMul
      (ε E ψ μ x * ε E (ψ.scale (-1)) μ' (T x))
    map_zero' := by
      change ε E ψ μ 0 * ε E (ψ.scale (-1)) μ' (T 0) = 1
      rw [map_zero, value_zero hε, value_zero hε, mul_one]
    map_add' x y := by
      change ε E ψ μ (x + y) * ε E (ψ.scale (-1)) μ' (T (x + y)) =
        (ε E ψ μ x * ε E (ψ.scale (-1)) μ' (T x)) *
        (ε E ψ μ y * ε E (ψ.scale (-1)) μ' (T y))
      rw [map_add, hε, hε]
      exact mul_mul_mul_comm _ _ _ _
  }

/-- The exact virtual elements on which the supplied fixed-Haar product is
one. Its submodule structure is proved from additivity, without any duality
or Fourier inversion premise. -/
def dualityKernel (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E) :
    Submodule ℤ (Virtual.{uF, uV} F E) :=
  LinearMap.ker (dualityDefect F ε hε E ψ μ μ').toIntLinearMap

@[simp]
theorem mem_dualityKernel (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E)
    (x : Virtual.{uF, uV} F E) :
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    x ∈ dualityKernel F ε hε E ψ μ μ' ↔
      ε E ψ μ x * ε E (ψ.scale (-1)) μ'
        (ExactGrothendieckGroup.continuousTwist
          (CommonClosureWeilDeligne.normCharacter F E)
          (ExactGrothendieckGroup.continuousDual x)) = 1 := Iff.rfl

/-- The published actual degree-zero generation assertion, together with the duality
equation on each displayed generator and on the trivial line, suffices for
the equation on every exact virtual element. All unproved mathematical
inputs are explicit premises of this auxiliary reduction. -/
theorem dualityKernel_eq_top_of_commonClosureDegreeZeroGeneration
    (hgen : CommonClosureDegreeZeroGeneration.{uF, uV} F)
    (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E)
    (htrivial : ExactGrothendieckGroup.characterClass
        (1 : weilSubgroup F E →ₜ* ℂˣ) ∈ dualityKernel F ε hε E ψ μ μ')
    (hgenerators : characterDifferenceInductionGenerators.{uF, uV} F E ⊆
      dualityKernel F ε hε E ψ μ μ') :
    dualityKernel F ε hε E ψ μ μ' = ⊤ := by
  have hzero : DegreeZero.{uF, uV} F E ≤ dualityKernel F ε hε E ψ μ μ' := by
    rw [← hgen E]
    exact Submodule.span_le.mpr hgenerators
  apply top_unique
  intro x _
  let t : Virtual.{uF, uV} F E :=
    ExactGrothendieckGroup.characterClass (1 : weilSubgroup F E →ₜ* ℂˣ)
  have hy : x - degree F E x • t ∈ DegreeZero.{uF, uV} F E := by
    change degree F E (x - degree F E x • t) = 0
    simp [t]
  have ht : degree F E x • t ∈ dualityKernel F ε hε E ψ μ μ' :=
    (dualityKernel F ε hε E ψ μ μ').smul_mem (degree F E x) htrivial
  have hx := (dualityKernel F ε hε E ψ μ μ').add_mem (hzero hy) ht
  simpa only [sub_add_cancel] using hx

end Langlands.LocalFactor.NonabelianSystem
