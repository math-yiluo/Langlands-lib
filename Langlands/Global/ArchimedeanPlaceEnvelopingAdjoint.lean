import Langlands.Algebra.LieEnvelopingEquiv
import Langlands.Global.ArchimedeanPlaceAdjoint
import Langlands.Global.ArchimedeanPlaceEnveloping

/-! # Actual unitary matrix adjoints on whole place enveloping algebras -/

noncomputable section
universe u v

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual unitary matrix adjoint on the entire local universal enveloping algebra. -/
def unitaryMatrixEnvelopingConjugation (𝕜 : Type v) [RCLike 𝕜] (n : ℕ)
    (k : Matrix.unitaryGroup (Fin n) 𝕜) :
    UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) ≃ₐ[ℂ]
      UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) :=
  Langlands.Algebra.LieEnvelopingEquiv.enveloping
    (unitaryMatrixComplexLieConjugation 𝕜 n k)

@[simp] theorem unitaryMatrixEnvelopingConjugation_generator
    (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) (k : Matrix.unitaryGroup (Fin n) 𝕜)
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) :
    unitaryMatrixEnvelopingConjugation 𝕜 n k (UniversalEnvelopingAlgebra.ι ℂ X) =
      UniversalEnvelopingAlgebra.ι ℂ (unitaryMatrixComplexLieConjugation 𝕜 n k X) :=
  Langlands.Algebra.LieEnvelopingEquiv.enveloping_generator _ X

@[simp] theorem unitaryMatrixComplexLieConjugation_one
    (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) :
    unitaryMatrixComplexLieConjugation 𝕜 n 1 = LieEquiv.refl := by
  apply LieEquiv.ext
  intro X
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp
  | add X Y hX hY => simp only [map_add, hX, hY]

theorem unitaryMatrixComplexLieConjugation_mul
    (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) (k l : Matrix.unitaryGroup (Fin n) 𝕜) :
    unitaryMatrixComplexLieConjugation 𝕜 n (k * l) =
      (unitaryMatrixComplexLieConjugation 𝕜 n l).trans
        (unitaryMatrixComplexLieConjugation 𝕜 n k) := by
  apply LieEquiv.ext
  intro X
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp [unitaryMatrixRealLieConjugation_apply, mul_assoc]
  | add X Y hX hY => simp only [map_add, hX, hY]

@[simp] theorem unitaryMatrixEnvelopingConjugation_one
    (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) :
    unitaryMatrixEnvelopingConjugation 𝕜 n 1 = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change unitaryMatrixEnvelopingConjugation 𝕜 n 1
    (UniversalEnvelopingAlgebra.ι ℂ X) = UniversalEnvelopingAlgebra.ι ℂ X
  rw [unitaryMatrixEnvelopingConjugation_generator,
    unitaryMatrixComplexLieConjugation_one]
  rfl

theorem unitaryMatrixEnvelopingConjugation_mul
    (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) (k l : Matrix.unitaryGroup (Fin n) 𝕜) :
    unitaryMatrixEnvelopingConjugation 𝕜 n (k * l) =
      (unitaryMatrixEnvelopingConjugation 𝕜 n l).trans
        (unitaryMatrixEnvelopingConjugation 𝕜 n k) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change unitaryMatrixEnvelopingConjugation 𝕜 n (k * l)
      (UniversalEnvelopingAlgebra.ι ℂ X) =
    unitaryMatrixEnvelopingConjugation 𝕜 n k
      (unitaryMatrixEnvelopingConjugation 𝕜 n l (UniversalEnvelopingAlgebra.ι ℂ X))
  simp only [unitaryMatrixEnvelopingConjugation_generator,
    unitaryMatrixComplexLieConjugation_mul, LieEquiv.trans_apply]

@[simp] theorem unitaryMatrixEnvelopingConjugation_inv
    (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) (k : Matrix.unitaryGroup (Fin n) 𝕜) :
    unitaryMatrixEnvelopingConjugation 𝕜 n k⁻¹ =
      (unitaryMatrixEnvelopingConjugation 𝕜 n k).symm := by
  apply AlgEquiv.ext
  intro a
  apply (unitaryMatrixEnvelopingConjugation 𝕜 n k).injective
  have h := congrArg
    (fun e : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) ≃ₐ[ℂ]
      UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) => e a)
    (unitaryMatrixEnvelopingConjugation_mul 𝕜 n k k⁻¹)
  simpa using h.symm

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- Global conjugation preserves the whole actual real-place enveloping image. -/
theorem envelopingConjugation_realInclusion_comp (p : ArchimedeanCompactFactors F n)
    (v : RP) :
    (envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)).toAlgHom.comp
        (realPlaceEnvelopingInclusion F n v) =
      (realPlaceEnvelopingInclusion F n v).comp
        (unitaryMatrixEnvelopingConjugation ℝ n (p.1 v)).toAlgHom := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
      (realPlaceEnvelopingInclusion F n v (realPlaceEnvelopingGenerator n X)) =
    realPlaceEnvelopingInclusion F n v
      (unitaryMatrixEnvelopingConjugation ℝ n (p.1 v)
        (UniversalEnvelopingAlgebra.ι ℂ X))
  rw [realPlaceEnvelopingInclusion_generator, envelopingConjugation_generator,
    complexLieConjugation_realInclusion, unitaryMatrixEnvelopingConjugation_generator]
  exact (realPlaceEnvelopingInclusion_generator F n v _).symm

theorem envelopingConjugation_complexInclusion_comp (p : ArchimedeanCompactFactors F n)
    (v : CP) :
    (envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)).toAlgHom.comp
        (complexPlaceEnvelopingInclusion F n v) =
      (complexPlaceEnvelopingInclusion F n v).comp
        (unitaryMatrixEnvelopingConjugation ℂ n (p.2 v)).toAlgHom := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
      (complexPlaceEnvelopingInclusion F n v (complexPlaceEnvelopingGenerator n X)) =
    complexPlaceEnvelopingInclusion F n v
      (unitaryMatrixEnvelopingConjugation ℂ n (p.2 v)
        (UniversalEnvelopingAlgebra.ι ℂ X))
  rw [complexPlaceEnvelopingInclusion_generator, envelopingConjugation_generator,
    complexLieConjugation_complexInclusion, unitaryMatrixEnvelopingConjugation_generator]
  exact (complexPlaceEnvelopingInclusion_generator F n v _).symm

@[simp] theorem envelopingConjugation_realInclusion (p : ArchimedeanCompactFactors F n)
    (v : RP) (a : RealPlaceEnvelopingAlgebra n) :
    envelopingConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
        (realPlaceEnvelopingInclusion F n v a) =
      realPlaceEnvelopingInclusion F n v (unitaryMatrixEnvelopingConjugation ℝ n (p.1 v) a) :=
  AlgHom.congr_fun (envelopingConjugation_realInclusion_comp F n p v) a

@[simp] theorem envelopingConjugation_complexInclusion (p : ArchimedeanCompactFactors F n)
    (v : CP) (a : ComplexPlaceEnvelopingAlgebra n) :
    envelopingConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
        (complexPlaceEnvelopingInclusion F n v a) =
      complexPlaceEnvelopingInclusion F n v (unitaryMatrixEnvelopingConjugation ℂ n (p.2 v) a) :=
  AlgHom.congr_fun (envelopingConjugation_complexInclusion_comp F n p v) a

end Langlands.Global.ArchimedeanGL
