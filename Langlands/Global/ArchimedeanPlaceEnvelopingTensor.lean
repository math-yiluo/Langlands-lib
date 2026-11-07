import Langlands.Global.ArchimedeanPlaceEnveloping
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Actual commuting place enveloping algebras and their tensor maps -/

noncomputable section
universe u v w

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Global.ArchimedeanGL

private theorem commute_enveloping_of_generators
    {L : Type v} [LieRing L] [LieAlgebra ℂ L]
    {A : Type w} [Ring A] [Algebra ℂ A]
    (f : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] A) (x : A)
    (hx : ∀ X, Commute x (f (UniversalEnvelopingAlgebra.ι ℂ X)))
    (a : UniversalEnvelopingAlgebra ℂ L) : Commute x (f a) := by
  refine Quotient.inductionOn a ?_
  intro t
  change Commute x (f ((UniversalEnvelopingAlgebra.mkAlgHom ℂ L) t))
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (Algebra.commutes z x).symm
  | ι X => exact hx X
  | mul a b ha hb => simpa only [map_mul] using ha.mul_right hb
  | add a b ha hb => simpa only [map_add] using ha.add_right hb

private theorem commute_enveloping_homs
    {L : Type v} [LieRing L] [LieAlgebra ℂ L]
    {M : Type w} [LieRing M] [LieAlgebra ℂ M]
    {A : Type u} [Ring A] [Algebra ℂ A]
    (f : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] A)
    (g : UniversalEnvelopingAlgebra ℂ M →ₐ[ℂ] A)
    (h : ∀ X Y, Commute (f (UniversalEnvelopingAlgebra.ι ℂ X))
      (g (UniversalEnvelopingAlgebra.ι ℂ Y)))
    (a : UniversalEnvelopingAlgebra ℂ L) (b : UniversalEnvelopingAlgebra ℂ M) :
    Commute (f a) (g b) := by
  exact (commute_enveloping_of_generators f (g b)
    (fun X => (commute_enveloping_of_generators g _ (h X) b).symm) a).symm

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

local instance realMatrixLieRing : LieRing RM :=
  LieRing.ofAssociativeRing
local instance complexMatrixLieRing : LieRing CM :=
  LieRing.ofAssociativeRing
local instance realMatrixRealLieAlgebra : LieAlgebra ℝ RM :=
  LieAlgebra.ofAssociativeAlgebra
local instance complexMatrixRealLieAlgebra : LieAlgebra ℝ CM :=
  LieAlgebra.ofAssociativeAlgebra
local instance coordinateMatrixLieRing : LieRing ((RP → RM) × (CP → CM)) :=
  LieRing.ofAssociativeRing

theorem realPlaceLieInclusions_lie_eq_zero (v w : RP) (h : v ≠ w) (X Y : RM) :
    ⁅realPlaceLieInclusion F n v X, realPlaceLieInclusion F n w Y⁆ = 0 := by
  apply (realLiePlaceCoordinates F n).injective
  apply Prod.ext
  · funext t
    change realPlaceLieProjection F n t _ = 0
    rw [LieHom.map_lie]
    by_cases ht : t = v
    · subst t
      simp [h]
    · simp [ht]
  · funext t
    change complexPlaceLieProjection F n t _ = 0
    simp only [LieHom.map_lie, complexProjection_realInclusion, lie_zero]

theorem complexPlaceLieInclusions_lie_eq_zero (v w : CP) (h : v ≠ w) (X Y : CM) :
    ⁅complexPlaceLieInclusion F n v X, complexPlaceLieInclusion F n w Y⁆ = 0 := by
  apply (realLiePlaceCoordinates F n).injective
  apply Prod.ext
  · funext t
    change realPlaceLieProjection F n t _ = 0
    simp only [LieHom.map_lie, realProjection_complexInclusion, lie_zero]
  · funext t
    change complexPlaceLieProjection F n t _ = 0
    rw [LieHom.map_lie]
    by_cases ht : t = v
    · subst t
      simp [h]
    · simp [ht]

theorem realComplexPlaceLieInclusions_lie_eq_zero (v : RP) (w : CP) (X : RM) (Y : CM) :
    ⁅realPlaceLieInclusion F n v X, complexPlaceLieInclusion F n w Y⁆ = 0 := by
  apply (realLiePlaceCoordinates F n).injective
  apply Prod.ext
  · funext t
    change realPlaceLieProjection F n t _ = 0
    simp only [LieHom.map_lie, realProjection_complexInclusion, lie_zero]
  · funext t
    change complexPlaceLieProjection F n t _ = 0
    simp only [LieHom.map_lie, complexProjection_realInclusion, zero_lie]

theorem realPlaceComplexLieInclusions_lie_eq_zero (v w : RP) (h : v ≠ w)
    (X Y : ℂ ⊗[ℝ] RM) :
    ⁅realPlaceComplexLieInclusion F n v X, realPlaceComplexLieInclusion F n w Y⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    induction Y using TensorProduct.inductionOn with
    | tmul t Y =>
      simp only [realPlaceComplexLieInclusion_tmul, complexLieAlgebra_lie_tmul,
        realPlaceLieInclusions_lie_eq_zero F n v w h, TensorProduct.tmul_zero]
    | add Y Z hY hZ => simp only [map_add, LieRing.lie_add, hY, hZ, add_zero]
  | add X Z hX hZ => simp only [map_add, LieRing.add_lie, hX, hZ, add_zero]

theorem complexPlaceComplexLieInclusions_lie_eq_zero (v w : CP) (h : v ≠ w)
    (X Y : ℂ ⊗[ℝ] CM) :
    ⁅complexPlaceComplexLieInclusion F n v X, complexPlaceComplexLieInclusion F n w Y⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    induction Y using TensorProduct.inductionOn with
    | tmul t Y =>
      simp only [complexPlaceComplexLieInclusion_tmul, complexLieAlgebra_lie_tmul,
        complexPlaceLieInclusions_lie_eq_zero F n v w h, TensorProduct.tmul_zero]
    | add Y Z hY hZ => simp only [map_add, LieRing.lie_add, hY, hZ, add_zero]
  | add X Z hX hZ => simp only [map_add, LieRing.add_lie, hX, hZ, add_zero]

theorem realComplexPlaceComplexLieInclusions_lie_eq_zero (v : RP) (w : CP)
    (X : ℂ ⊗[ℝ] RM) (Y : ℂ ⊗[ℝ] CM) :
    ⁅realPlaceComplexLieInclusion F n v X, complexPlaceComplexLieInclusion F n w Y⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    induction Y using TensorProduct.inductionOn with
    | tmul t Y =>
      simp only [realPlaceComplexLieInclusion_tmul, complexPlaceComplexLieInclusion_tmul,
        complexLieAlgebra_lie_tmul, realComplexPlaceLieInclusions_lie_eq_zero,
        TensorProduct.tmul_zero]
    | add Y Z hY hZ => simp only [map_add, LieRing.lie_add, hY, hZ, add_zero]
  | add X Z hX hZ => simp only [map_add, LieRing.add_lie, hX, hZ, add_zero]

private theorem envelopingGenerator_commute_of_lie_zero
    (X Y : ComplexLieAlgebra F n) (h : ⁅X, Y⁆ = 0) :
    Commute (envelopingGenerator F n X) (envelopingGenerator F n Y) := by
  change envelopingGenerator F n X * envelopingGenerator F n Y =
    envelopingGenerator F n Y * envelopingGenerator F n X
  apply sub_eq_zero.mp
  rw [← envelopingGenerator_lie, h, map_zero]

/-- The full real-place enveloping images commute at distinct places. -/
theorem realPlaceEnvelopingInclusions_commute (v w : RP) (h : v ≠ w)
    (a b : RealPlaceEnvelopingAlgebra n) :
    Commute (realPlaceEnvelopingInclusion F n v a) (realPlaceEnvelopingInclusion F n w b) := by
  apply commute_enveloping_homs
  intro X Y
  change Commute
    (realPlaceEnvelopingInclusion F n v (realPlaceEnvelopingGenerator n X))
    (realPlaceEnvelopingInclusion F n w (realPlaceEnvelopingGenerator n Y))
  rw [realPlaceEnvelopingInclusion_generator, realPlaceEnvelopingInclusion_generator]
  exact envelopingGenerator_commute_of_lie_zero F n _ _
    (realPlaceComplexLieInclusions_lie_eq_zero F n v w h X Y)

theorem complexPlaceEnvelopingInclusions_commute (v w : CP) (h : v ≠ w)
    (a b : ComplexPlaceEnvelopingAlgebra n) :
    Commute (complexPlaceEnvelopingInclusion F n v a)
      (complexPlaceEnvelopingInclusion F n w b) := by
  apply commute_enveloping_homs
  intro X Y
  change Commute
    (complexPlaceEnvelopingInclusion F n v (complexPlaceEnvelopingGenerator n X))
    (complexPlaceEnvelopingInclusion F n w (complexPlaceEnvelopingGenerator n Y))
  rw [complexPlaceEnvelopingInclusion_generator, complexPlaceEnvelopingInclusion_generator]
  exact envelopingGenerator_commute_of_lie_zero F n _ _
    (complexPlaceComplexLieInclusions_lie_eq_zero F n v w h X Y)

theorem realComplexPlaceEnvelopingInclusions_commute (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n) (b : ComplexPlaceEnvelopingAlgebra n) :
    Commute (realPlaceEnvelopingInclusion F n v a)
      (complexPlaceEnvelopingInclusion F n w b) := by
  apply commute_enveloping_homs
  intro X Y
  change Commute
    (realPlaceEnvelopingInclusion F n v (realPlaceEnvelopingGenerator n X))
    (complexPlaceEnvelopingInclusion F n w (complexPlaceEnvelopingGenerator n Y))
  rw [realPlaceEnvelopingInclusion_generator, complexPlaceEnvelopingInclusion_generator]
  exact envelopingGenerator_commute_of_lie_zero F n _ _
    (realComplexPlaceComplexLieInclusions_lie_eq_zero F n v w X Y)

/-- Multiply the two actual commuting real-place enveloping images. -/
def realPlacesEnvelopingTensorMap (v w : RP) (h : v ≠ w) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      EnvelopingAlgebra F n :=
  Algebra.TensorProduct.lift (realPlaceEnvelopingInclusion F n v)
    (realPlaceEnvelopingInclusion F n w) (realPlaceEnvelopingInclusions_commute F n v w h)

def complexPlacesEnvelopingTensorMap (v w : CP) (h : v ≠ w) :
    (ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      EnvelopingAlgebra F n :=
  Algebra.TensorProduct.lift (complexPlaceEnvelopingInclusion F n v)
    (complexPlaceEnvelopingInclusion F n w) (complexPlaceEnvelopingInclusions_commute F n v w h)

def realComplexPlacesEnvelopingTensorMap (v : RP) (w : CP) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      EnvelopingAlgebra F n :=
  Algebra.TensorProduct.lift (realPlaceEnvelopingInclusion F n v)
    (complexPlaceEnvelopingInclusion F n w) (realComplexPlaceEnvelopingInclusions_commute F n v w)

@[simp] theorem realPlacesEnvelopingTensorMap_tmul (v w : RP) (h : v ≠ w)
    (a b : RealPlaceEnvelopingAlgebra n) :
    realPlacesEnvelopingTensorMap F n v w h (a ⊗ₜ[ℂ] b) =
      realPlaceEnvelopingInclusion F n v a * realPlaceEnvelopingInclusion F n w b := rfl

@[simp] theorem complexPlacesEnvelopingTensorMap_tmul (v w : CP) (h : v ≠ w)
    (a b : ComplexPlaceEnvelopingAlgebra n) :
    complexPlacesEnvelopingTensorMap F n v w h (a ⊗ₜ[ℂ] b) =
      complexPlaceEnvelopingInclusion F n v a * complexPlaceEnvelopingInclusion F n w b := rfl

@[simp] theorem realComplexPlacesEnvelopingTensorMap_tmul (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n) (b : ComplexPlaceEnvelopingAlgebra n) :
    realComplexPlacesEnvelopingTensorMap F n v w (a ⊗ₜ[ℂ] b) =
      realPlaceEnvelopingInclusion F n v a * complexPlaceEnvelopingInclusion F n w b := rfl

end Langlands.Global.ArchimedeanGL
