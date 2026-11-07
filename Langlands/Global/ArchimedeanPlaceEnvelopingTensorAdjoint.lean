import Langlands.Global.ArchimedeanPlaceEnvelopingAdjoint
import Langlands.Global.ArchimedeanPlaceEnvelopingTensor

/-! # Actual matrix adjoints on two-place enveloping tensor algebras -/

noncomputable section
universe u v w

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Global.ArchimedeanGL

local instance tensorAdjointMatrixLieRing (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) :
    LieRing (Matrix (Fin n) (Fin n) 𝕜) := LieRing.ofAssociativeRing
local instance tensorAdjointMatrixRealLieAlgebra (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) :
    LieAlgebra ℝ (Matrix (Fin n) (Fin n) 𝕜) := LieAlgebra.ofAssociativeAlgebra

/-- Independent actual matrix adjoints act on the tensor of their entire enveloping algebras. -/
def unitaryMatrixEnvelopingTensorConjugation
    (𝕜 : Type v) (𝕝 : Type w) [RCLike 𝕜] [RCLike 𝕝] (n m : ℕ)
    (k : Matrix.unitaryGroup (Fin n) 𝕜) (l : Matrix.unitaryGroup (Fin m) 𝕝) :
    (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) ⊗[ℂ]
      UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin m) (Fin m) 𝕝)) ≃ₐ[ℂ]
    (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) ⊗[ℂ]
      UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin m) (Fin m) 𝕝)) :=
  Algebra.TensorProduct.congr
    (unitaryMatrixEnvelopingConjugation 𝕜 n k)
    (unitaryMatrixEnvelopingConjugation 𝕝 m l)

@[simp] theorem unitaryMatrixEnvelopingTensorConjugation_tmul
    (𝕜 : Type v) (𝕝 : Type w) [RCLike 𝕜] [RCLike 𝕝] (n m : ℕ)
    (k : Matrix.unitaryGroup (Fin n) 𝕜) (l : Matrix.unitaryGroup (Fin m) 𝕝)
    (a : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜))
    (b : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin m) (Fin m) 𝕝)) :
    unitaryMatrixEnvelopingTensorConjugation 𝕜 𝕝 n m k l (a ⊗ₜ[ℂ] b) =
      unitaryMatrixEnvelopingConjugation 𝕜 n k a ⊗ₜ[ℂ]
        unitaryMatrixEnvelopingConjugation 𝕝 m l b := rfl

@[simp] theorem unitaryMatrixEnvelopingTensorConjugation_one
    (𝕜 : Type v) (𝕝 : Type w) [RCLike 𝕜] [RCLike 𝕝] (n m : ℕ) :
    unitaryMatrixEnvelopingTensorConjugation 𝕜 𝕝 n m 1 1 = AlgEquiv.refl := by
  simp only [unitaryMatrixEnvelopingTensorConjugation,
    unitaryMatrixEnvelopingConjugation_one, Algebra.TensorProduct.congr_refl]

theorem unitaryMatrixEnvelopingTensorConjugation_mul
    (𝕜 : Type v) (𝕝 : Type w) [RCLike 𝕜] [RCLike 𝕝] (n m : ℕ)
    (k k' : Matrix.unitaryGroup (Fin n) 𝕜) (l l' : Matrix.unitaryGroup (Fin m) 𝕝) :
    unitaryMatrixEnvelopingTensorConjugation 𝕜 𝕝 n m (k * k') (l * l') =
      (unitaryMatrixEnvelopingTensorConjugation 𝕜 𝕝 n m k' l').trans
        (unitaryMatrixEnvelopingTensorConjugation 𝕜 𝕝 n m k l) := by
  simp only [unitaryMatrixEnvelopingTensorConjugation,
    unitaryMatrixEnvelopingConjugation_mul, Algebra.TensorProduct.congr_trans]

@[simp] theorem unitaryMatrixEnvelopingTensorConjugation_inv
    (𝕜 : Type v) (𝕝 : Type w) [RCLike 𝕜] [RCLike 𝕝] (n m : ℕ)
    (k : Matrix.unitaryGroup (Fin n) 𝕜) (l : Matrix.unitaryGroup (Fin m) 𝕝) :
    unitaryMatrixEnvelopingTensorConjugation 𝕜 𝕝 n m k⁻¹ l⁻¹ =
      (unitaryMatrixEnvelopingTensorConjugation 𝕜 𝕝 n m k l).symm := by
  simp only [unitaryMatrixEnvelopingTensorConjugation,
    unitaryMatrixEnvelopingConjugation_inv, Algebra.TensorProduct.congr_symm]

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- The actual global adjoint and real/real tensor map commute as algebra homomorphisms. -/
theorem envelopingConjugation_realPlacesTensorMap_comp
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w) :
    (envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)).toAlgHom.comp
        (realPlacesEnvelopingTensorMap F n v w h) =
      (realPlacesEnvelopingTensorMap F n v w h).comp
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℝ n n (p.1 v) (p.1 w)).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
      (realPlacesEnvelopingTensorMap F n v w h (a ⊗ₜ[ℂ] b)) =
    realPlacesEnvelopingTensorMap F n v w h
      (unitaryMatrixEnvelopingTensorConjugation ℝ ℝ n n (p.1 v) (p.1 w) (a ⊗ₜ[ℂ] b))
  simp only [realPlacesEnvelopingTensorMap_tmul,
    unitaryMatrixEnvelopingTensorConjugation_tmul, map_mul,
    envelopingConjugation_realInclusion]

theorem envelopingConjugation_complexPlacesTensorMap_comp
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w) :
    (envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)).toAlgHom.comp
        (complexPlacesEnvelopingTensorMap F n v w h) =
      (complexPlacesEnvelopingTensorMap F n v w h).comp
        (unitaryMatrixEnvelopingTensorConjugation ℂ ℂ n n (p.2 v) (p.2 w)).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
      (complexPlacesEnvelopingTensorMap F n v w h (a ⊗ₜ[ℂ] b)) =
    complexPlacesEnvelopingTensorMap F n v w h
      (unitaryMatrixEnvelopingTensorConjugation ℂ ℂ n n (p.2 v) (p.2 w) (a ⊗ₜ[ℂ] b))
  simp only [complexPlacesEnvelopingTensorMap_tmul,
    unitaryMatrixEnvelopingTensorConjugation_tmul, map_mul,
    envelopingConjugation_complexInclusion]

theorem envelopingConjugation_realComplexPlacesTensorMap_comp
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP) :
    (envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)).toAlgHom.comp
        (realComplexPlacesEnvelopingTensorMap F n v w) =
      (realComplexPlacesEnvelopingTensorMap F n v w).comp
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℂ n n (p.1 v) (p.2 w)).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change envelopingConjugation F n
      (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
      (realComplexPlacesEnvelopingTensorMap F n v w (a ⊗ₜ[ℂ] b)) =
    realComplexPlacesEnvelopingTensorMap F n v w
      (unitaryMatrixEnvelopingTensorConjugation ℝ ℂ n n (p.1 v) (p.2 w) (a ⊗ₜ[ℂ] b))
  simp only [realComplexPlacesEnvelopingTensorMap_tmul,
    unitaryMatrixEnvelopingTensorConjugation_tmul, map_mul,
    envelopingConjugation_realInclusion, envelopingConjugation_complexInclusion]

@[simp] theorem envelopingConjugation_realPlacesTensorMap
    (p : ArchimedeanCompactFactors F n) (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) :
    envelopingConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
        (realPlacesEnvelopingTensorMap F n v w h a) =
      realPlacesEnvelopingTensorMap F n v w h
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℝ n n (p.1 v) (p.1 w) a) :=
  AlgHom.congr_fun (envelopingConjugation_realPlacesTensorMap_comp F n p v w h) a

@[simp] theorem envelopingConjugation_complexPlacesTensorMap
    (p : ArchimedeanCompactFactors F n) (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) :
    envelopingConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
        (complexPlacesEnvelopingTensorMap F n v w h a) =
      complexPlacesEnvelopingTensorMap F n v w h
        (unitaryMatrixEnvelopingTensorConjugation ℂ ℂ n n (p.2 v) (p.2 w) a) :=
  AlgHom.congr_fun (envelopingConjugation_complexPlacesTensorMap_comp F n p v w h) a

@[simp] theorem envelopingConjugation_realComplexPlacesTensorMap
    (p : ArchimedeanCompactFactors F n) (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) :
    envelopingConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
        (realComplexPlacesEnvelopingTensorMap F n v w a) =
      realComplexPlacesEnvelopingTensorMap F n v w
        (unitaryMatrixEnvelopingTensorConjugation ℝ ℂ n n (p.1 v) (p.2 w) a) :=
  AlgHom.congr_fun (envelopingConjugation_realComplexPlacesTensorMap_comp F n p v w) a

end Langlands.Global.ArchimedeanGL
