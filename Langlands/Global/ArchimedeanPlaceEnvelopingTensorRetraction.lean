import Langlands.Global.ArchimedeanPlaceEnvelopingTensor
import Langlands.Algebra.EnvelopingTensorProjection

/-! # Actual two-place tensor retractions of the global enveloping algebra -/

noncomputable section
universe u

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

@[simp] theorem realPlaceComplexLieProjection_otherInclusion
    (v w : RP) (h : v ≠ w) (X : ℂ ⊗[ℝ] RM) :
    realPlaceComplexLieProjection F n v (realPlaceComplexLieInclusion F n w X) = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [realPlaceComplexLieInclusion_tmul, realPlaceComplexLieProjection_tmul,
      realProjection_realInclusion, Pi.single_eq_of_ne h, TensorProduct.tmul_zero]
  | add X Y hX hY => simp only [map_add, hX, hY, add_zero]

@[simp] theorem complexPlaceComplexLieProjection_otherInclusion
    (v w : CP) (h : v ≠ w) (X : ℂ ⊗[ℝ] CM) :
    complexPlaceComplexLieProjection F n v (complexPlaceComplexLieInclusion F n w X) = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexPlaceComplexLieInclusion_tmul, complexPlaceComplexLieProjection_tmul,
      complexProjection_complexInclusion, Pi.single_eq_of_ne h, TensorProduct.tmul_zero]
  | add X Y hX hY => simp only [map_add, hX, hY, add_zero]

@[simp] theorem realPlaceComplexLieProjection_complexInclusion
    (v : RP) (w : CP) (X : ℂ ⊗[ℝ] CM) :
    realPlaceComplexLieProjection F n v (complexPlaceComplexLieInclusion F n w X) = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexPlaceComplexLieInclusion_tmul, realPlaceComplexLieProjection_tmul,
      realProjection_complexInclusion, TensorProduct.tmul_zero]
  | add X Y hX hY => simp only [map_add, hX, hY, add_zero]

@[simp] theorem complexPlaceComplexLieProjection_realInclusion
    (v : CP) (w : RP) (X : ℂ ⊗[ℝ] RM) :
    complexPlaceComplexLieProjection F n v (realPlaceComplexLieInclusion F n w X) = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [realPlaceComplexLieInclusion_tmul, complexPlaceComplexLieProjection_tmul,
      complexProjection_realInclusion, TensorProduct.tmul_zero]
  | add X Y hX hY => simp only [map_add, hX, hY, add_zero]

/-- The enveloping lift of the two actual real-place coordinate Lie maps. -/
def realPlacesEnvelopingTensorProjection (v w : RP) :
    EnvelopingAlgebra F n →ₐ[ℂ]
      (RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) :=
  Langlands.Algebra.EnvelopingTensor.lift ℂ
    ((realPlaceEnvelopingGenerator n).comp (realPlaceComplexLieProjection F n v))
    ((realPlaceEnvelopingGenerator n).comp (realPlaceComplexLieProjection F n w))

/-- Both factors retain the full complexification of the underlying real local Lie algebra. -/
def complexPlacesEnvelopingTensorProjection (v w : CP) :
    EnvelopingAlgebra F n →ₐ[ℂ]
      (ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) :=
  Langlands.Algebra.EnvelopingTensor.lift ℂ
    ((complexPlaceEnvelopingGenerator n).comp (complexPlaceComplexLieProjection F n v))
    ((complexPlaceEnvelopingGenerator n).comp (complexPlaceComplexLieProjection F n w))

/-- Actual real and complex coordinate directions give an algebra map to their local tensor. -/
def realComplexPlacesEnvelopingTensorProjection (v : RP) (w : CP) :
    EnvelopingAlgebra F n →ₐ[ℂ]
      (RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) :=
  Langlands.Algebra.EnvelopingTensor.lift ℂ
    ((realPlaceEnvelopingGenerator n).comp (realPlaceComplexLieProjection F n v))
    ((complexPlaceEnvelopingGenerator n).comp (complexPlaceComplexLieProjection F n w))

@[simp] theorem realPlacesEnvelopingTensorProjection_generator (v w : RP)
    (X : ComplexLieAlgebra F n) :
    realPlacesEnvelopingTensorProjection F n v w (envelopingGenerator F n X) =
      realPlaceEnvelopingGenerator n (realPlaceComplexLieProjection F n v X) ⊗ₜ[ℂ] 1 +
        1 ⊗ₜ[ℂ] realPlaceEnvelopingGenerator n (realPlaceComplexLieProjection F n w X) :=
  Langlands.Algebra.EnvelopingTensor.lift_generator ℂ _ _ X

@[simp] theorem complexPlacesEnvelopingTensorProjection_generator (v w : CP)
    (X : ComplexLieAlgebra F n) :
    complexPlacesEnvelopingTensorProjection F n v w (envelopingGenerator F n X) =
      complexPlaceEnvelopingGenerator n (complexPlaceComplexLieProjection F n v X) ⊗ₜ[ℂ] 1 +
        1 ⊗ₜ[ℂ] complexPlaceEnvelopingGenerator n (complexPlaceComplexLieProjection F n w X) :=
  Langlands.Algebra.EnvelopingTensor.lift_generator ℂ _ _ X

@[simp] theorem realComplexPlacesEnvelopingTensorProjection_generator (v : RP) (w : CP)
    (X : ComplexLieAlgebra F n) :
    realComplexPlacesEnvelopingTensorProjection F n v w (envelopingGenerator F n X) =
      realPlaceEnvelopingGenerator n (realPlaceComplexLieProjection F n v X) ⊗ₜ[ℂ] 1 +
        1 ⊗ₜ[ℂ] complexPlaceEnvelopingGenerator n (complexPlaceComplexLieProjection F n w X) :=
  Langlands.Algebra.EnvelopingTensor.lift_generator ℂ _ _ X

theorem realPlacesEnvelopingTensorProjection_comp_left (v w : RP) (h : v ≠ w) :
    (realPlacesEnvelopingTensorProjection F n v w).comp (realPlaceEnvelopingInclusion F n v) =
      Algebra.TensorProduct.includeLeft := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change realPlacesEnvelopingTensorProjection F n v w
    (realPlaceEnvelopingInclusion F n v (realPlaceEnvelopingGenerator n X)) =
      realPlaceEnvelopingGenerator n X ⊗ₜ[ℂ] 1
  rw [realPlaceEnvelopingInclusion_generator, realPlacesEnvelopingTensorProjection_generator]
  simp only [realPlaceComplexLieProjection_inclusion,
    realPlaceComplexLieProjection_otherInclusion F n w v h.symm, map_zero,
    TensorProduct.tmul_zero, add_zero]

theorem realPlacesEnvelopingTensorProjection_comp_right (v w : RP) (h : v ≠ w) :
    (realPlacesEnvelopingTensorProjection F n v w).comp (realPlaceEnvelopingInclusion F n w) =
      Algebra.TensorProduct.includeRight := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change realPlacesEnvelopingTensorProjection F n v w
    (realPlaceEnvelopingInclusion F n w (realPlaceEnvelopingGenerator n X)) =
      1 ⊗ₜ[ℂ] realPlaceEnvelopingGenerator n X
  rw [realPlaceEnvelopingInclusion_generator, realPlacesEnvelopingTensorProjection_generator]
  simp only [realPlaceComplexLieProjection_inclusion,
    realPlaceComplexLieProjection_otherInclusion F n v w h, map_zero,
    TensorProduct.zero_tmul, zero_add]

@[simp] theorem realPlacesEnvelopingTensorProjection_leftInclusion (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n) :
    realPlacesEnvelopingTensorProjection F n v w (realPlaceEnvelopingInclusion F n v a) =
      a ⊗ₜ[ℂ] 1 :=
  AlgHom.congr_fun (realPlacesEnvelopingTensorProjection_comp_left F n v w h) a

@[simp] theorem realPlacesEnvelopingTensorProjection_rightInclusion (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n) :
    realPlacesEnvelopingTensorProjection F n v w (realPlaceEnvelopingInclusion F n w a) =
      1 ⊗ₜ[ℂ] a :=
  AlgHom.congr_fun (realPlacesEnvelopingTensorProjection_comp_right F n v w h) a

/-- The actual two-place tensor map has the constructed algebra retraction. -/
theorem realPlacesEnvelopingTensorProjection_comp_map (v w : RP) (h : v ≠ w) :
    (realPlacesEnvelopingTensorProjection F n v w).comp (realPlacesEnvelopingTensorMap F n v w h) =
      AlgHom.id ℂ (RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change realPlacesEnvelopingTensorProjection F n v w
    (realPlacesEnvelopingTensorMap F n v w h (a ⊗ₜ[ℂ] b)) = a ⊗ₜ[ℂ] b
  rw [realPlacesEnvelopingTensorMap_tmul, map_mul,
    realPlacesEnvelopingTensorProjection_leftInclusion F n v w h,
    realPlacesEnvelopingTensorProjection_rightInclusion F n v w h,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

@[simp] theorem realPlacesEnvelopingTensorProjection_map (v w : RP) (h : v ≠ w)
    (t : (RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n)) :
    realPlacesEnvelopingTensorProjection F n v w (realPlacesEnvelopingTensorMap F n v w h t) = t :=
  AlgHom.congr_fun (realPlacesEnvelopingTensorProjection_comp_map F n v w h) t

theorem realPlacesEnvelopingTensorMap_injective (v w : RP) (h : v ≠ w) :
    Function.Injective (realPlacesEnvelopingTensorMap F n v w h) := by
  intro a b hab
  simpa only [realPlacesEnvelopingTensorProjection_map] using
    congrArg (realPlacesEnvelopingTensorProjection F n v w) hab

theorem realPlacesEnvelopingTensorProjection_surjective (v w : RP) (h : v ≠ w) :
    Function.Surjective (realPlacesEnvelopingTensorProjection F n v w) :=
  fun t => ⟨realPlacesEnvelopingTensorMap F n v w h t,
    realPlacesEnvelopingTensorProjection_map F n v w h t⟩

theorem complexPlacesEnvelopingTensorProjection_comp_left (v w : CP) (h : v ≠ w) :
    (complexPlacesEnvelopingTensorProjection F n v w).comp (complexPlaceEnvelopingInclusion F n v) =
      Algebra.TensorProduct.includeLeft := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change complexPlacesEnvelopingTensorProjection F n v w
    (complexPlaceEnvelopingInclusion F n v (complexPlaceEnvelopingGenerator n X)) =
      complexPlaceEnvelopingGenerator n X ⊗ₜ[ℂ] 1
  rw [complexPlaceEnvelopingInclusion_generator, complexPlacesEnvelopingTensorProjection_generator]
  simp only [complexPlaceComplexLieProjection_inclusion,
    complexPlaceComplexLieProjection_otherInclusion F n w v h.symm, map_zero,
    TensorProduct.tmul_zero, add_zero]

theorem complexPlacesEnvelopingTensorProjection_comp_right (v w : CP) (h : v ≠ w) :
    (complexPlacesEnvelopingTensorProjection F n v w).comp (complexPlaceEnvelopingInclusion F n w) =
      Algebra.TensorProduct.includeRight := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change complexPlacesEnvelopingTensorProjection F n v w
    (complexPlaceEnvelopingInclusion F n w (complexPlaceEnvelopingGenerator n X)) =
      1 ⊗ₜ[ℂ] complexPlaceEnvelopingGenerator n X
  rw [complexPlaceEnvelopingInclusion_generator, complexPlacesEnvelopingTensorProjection_generator]
  simp only [complexPlaceComplexLieProjection_inclusion,
    complexPlaceComplexLieProjection_otherInclusion F n v w h, map_zero,
    TensorProduct.zero_tmul, zero_add]

@[simp] theorem complexPlacesEnvelopingTensorProjection_leftInclusion (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n) :
    complexPlacesEnvelopingTensorProjection F n v w (complexPlaceEnvelopingInclusion F n v a) =
      a ⊗ₜ[ℂ] 1 :=
  AlgHom.congr_fun (complexPlacesEnvelopingTensorProjection_comp_left F n v w h) a

@[simp] theorem complexPlacesEnvelopingTensorProjection_rightInclusion (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n) :
    complexPlacesEnvelopingTensorProjection F n v w (complexPlaceEnvelopingInclusion F n w a) =
      1 ⊗ₜ[ℂ] a :=
  AlgHom.congr_fun (complexPlacesEnvelopingTensorProjection_comp_right F n v w h) a

/-- The actual two-place tensor map has the constructed algebra retraction. -/
theorem complexPlacesEnvelopingTensorProjection_comp_map (v w : CP) (h : v ≠ w) :
    (complexPlacesEnvelopingTensorProjection F n v w).comp (complexPlacesEnvelopingTensorMap F n v w h) =
      AlgHom.id ℂ (ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change complexPlacesEnvelopingTensorProjection F n v w
    (complexPlacesEnvelopingTensorMap F n v w h (a ⊗ₜ[ℂ] b)) = a ⊗ₜ[ℂ] b
  rw [complexPlacesEnvelopingTensorMap_tmul, map_mul,
    complexPlacesEnvelopingTensorProjection_leftInclusion F n v w h,
    complexPlacesEnvelopingTensorProjection_rightInclusion F n v w h,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

@[simp] theorem complexPlacesEnvelopingTensorProjection_map (v w : CP) (h : v ≠ w)
    (t : (ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n)) :
    complexPlacesEnvelopingTensorProjection F n v w (complexPlacesEnvelopingTensorMap F n v w h t) = t :=
  AlgHom.congr_fun (complexPlacesEnvelopingTensorProjection_comp_map F n v w h) t

theorem complexPlacesEnvelopingTensorMap_injective (v w : CP) (h : v ≠ w) :
    Function.Injective (complexPlacesEnvelopingTensorMap F n v w h) := by
  intro a b hab
  simpa only [complexPlacesEnvelopingTensorProjection_map] using
    congrArg (complexPlacesEnvelopingTensorProjection F n v w) hab

theorem complexPlacesEnvelopingTensorProjection_surjective (v w : CP) (h : v ≠ w) :
    Function.Surjective (complexPlacesEnvelopingTensorProjection F n v w) :=
  fun t => ⟨complexPlacesEnvelopingTensorMap F n v w h t,
    complexPlacesEnvelopingTensorProjection_map F n v w h t⟩

theorem realComplexPlacesEnvelopingTensorProjection_comp_left (v : RP) (w : CP) :
    (realComplexPlacesEnvelopingTensorProjection F n v w).comp (realPlaceEnvelopingInclusion F n v) =
      Algebra.TensorProduct.includeLeft := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change realComplexPlacesEnvelopingTensorProjection F n v w
    (realPlaceEnvelopingInclusion F n v (realPlaceEnvelopingGenerator n X)) =
      realPlaceEnvelopingGenerator n X ⊗ₜ[ℂ] 1
  rw [realPlaceEnvelopingInclusion_generator, realComplexPlacesEnvelopingTensorProjection_generator]
  simp only [realPlaceComplexLieProjection_inclusion,
    complexPlaceComplexLieProjection_realInclusion, map_zero,
    TensorProduct.tmul_zero, add_zero]

theorem realComplexPlacesEnvelopingTensorProjection_comp_right (v : RP) (w : CP) :
    (realComplexPlacesEnvelopingTensorProjection F n v w).comp (complexPlaceEnvelopingInclusion F n w) =
      Algebra.TensorProduct.includeRight := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change realComplexPlacesEnvelopingTensorProjection F n v w
    (complexPlaceEnvelopingInclusion F n w (complexPlaceEnvelopingGenerator n X)) =
      1 ⊗ₜ[ℂ] complexPlaceEnvelopingGenerator n X
  rw [complexPlaceEnvelopingInclusion_generator, realComplexPlacesEnvelopingTensorProjection_generator]
  simp only [complexPlaceComplexLieProjection_inclusion,
    realPlaceComplexLieProjection_complexInclusion, map_zero,
    TensorProduct.zero_tmul, zero_add]

@[simp] theorem realComplexPlacesEnvelopingTensorProjection_leftInclusion (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n) :
    realComplexPlacesEnvelopingTensorProjection F n v w (realPlaceEnvelopingInclusion F n v a) =
      a ⊗ₜ[ℂ] 1 :=
  AlgHom.congr_fun (realComplexPlacesEnvelopingTensorProjection_comp_left F n v w) a

@[simp] theorem realComplexPlacesEnvelopingTensorProjection_rightInclusion (v : RP) (w : CP)
    (a : ComplexPlaceEnvelopingAlgebra n) :
    realComplexPlacesEnvelopingTensorProjection F n v w (complexPlaceEnvelopingInclusion F n w a) =
      1 ⊗ₜ[ℂ] a :=
  AlgHom.congr_fun (realComplexPlacesEnvelopingTensorProjection_comp_right F n v w) a

/-- The actual two-place tensor map has the constructed algebra retraction. -/
theorem realComplexPlacesEnvelopingTensorProjection_comp_map (v : RP) (w : CP) :
    (realComplexPlacesEnvelopingTensorProjection F n v w).comp (realComplexPlacesEnvelopingTensorMap F n v w) =
      AlgHom.id ℂ (RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change realComplexPlacesEnvelopingTensorProjection F n v w
    (realComplexPlacesEnvelopingTensorMap F n v w (a ⊗ₜ[ℂ] b)) = a ⊗ₜ[ℂ] b
  rw [realComplexPlacesEnvelopingTensorMap_tmul, map_mul,
    realComplexPlacesEnvelopingTensorProjection_leftInclusion F n v w,
    realComplexPlacesEnvelopingTensorProjection_rightInclusion F n v w,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

@[simp] theorem realComplexPlacesEnvelopingTensorProjection_map (v : RP) (w : CP)
    (t : (RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n)) :
    realComplexPlacesEnvelopingTensorProjection F n v w (realComplexPlacesEnvelopingTensorMap F n v w t) = t :=
  AlgHom.congr_fun (realComplexPlacesEnvelopingTensorProjection_comp_map F n v w) t

theorem realComplexPlacesEnvelopingTensorMap_injective (v : RP) (w : CP) :
    Function.Injective (realComplexPlacesEnvelopingTensorMap F n v w) := by
  intro a b hab
  simpa only [realComplexPlacesEnvelopingTensorProjection_map] using
    congrArg (realComplexPlacesEnvelopingTensorProjection F n v w) hab

theorem realComplexPlacesEnvelopingTensorProjection_surjective (v : RP) (w : CP) :
    Function.Surjective (realComplexPlacesEnvelopingTensorProjection F n v w) :=
  fun t => ⟨realComplexPlacesEnvelopingTensorMap F n v w t,
    realComplexPlacesEnvelopingTensorProjection_map F n v w t⟩

end Langlands.Global.ArchimedeanGL
