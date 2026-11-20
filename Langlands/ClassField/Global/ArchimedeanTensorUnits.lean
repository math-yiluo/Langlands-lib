import Langlands.ClassField.Global.TensorNormPrimitiveComparison
import Langlands.Global.AdelicFunctoriality.NormReduction
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Tensor units over an archimedean coefficient field -/

noncomputable section

universe u

open NumberField
open scoped TensorProduct NumberField.LiesOver
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.ClassField.Global.TensorUnitShapiro

open Langlands.Algebra Langlands.Global.AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F B : Type u} [Field F] [Field B] [NumberField F] [NumberField B] [Algebra F B]
  (v : InfinitePlace F) {M : Type u} [Field M] [Algebra v.Completion M] [Algebra F M]
  [IsScalarTower F v.Completion M]

local notation "K" => InfinitePlace.Completion v
local notation "I" => InfinitePlacesAbove B v

private def archimedeanCompletedTensorEquiv :
    M ⊗[F] B ≃ₐ[M] ((w : I) → M ⊗[K] w.1.Completion) := by
  classical
  exact (Algebra.TensorProduct.cancelBaseChange F K M M B).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[M] M)
      (infiniteTensorEquiv (L := B) v)).trans <|
    Algebra.TensorProduct.piRight K M M (fun w : I => w.1.Completion)

/-- The tensor algebra after extension from an infinite completion is the product
of the tensors with the fields of the completions above it. -/
def archimedeanTensorEquiv : B ⊗[F] M ≃+* ((w : I) → w.1.Completion ⊗[K] M) :=
  (Algebra.TensorProduct.comm F B M).toRingEquiv.trans <|
    (archimedeanCompletedTensorEquiv (B := B) (M := M) v).toRingEquiv.trans <|
    RingEquiv.piCongrRight fun w : I => (Algebra.TensorProduct.comm K M (w.1.Completion)).toRingEquiv

@[simp]
theorem archimedeanTensorEquiv_tmul (b : B) (m : M) (w : I) :
    archimedeanTensorEquiv v (b ⊗ₜ[F] m) w = algebraMap B (w.1.Completion) b ⊗ₜ[K] m := by
  change (Algebra.TensorProduct.comm K M (w.1.Completion))
    (archimedeanCompletedTensorEquiv v (m ⊗ₜ[F] b) w) = _
  simp [archimedeanCompletedTensorEquiv, infiniteTensorEquiv_apply]

/-- The resulting coordinates on the actual tensor units. -/
def archimedeanTensorUnitsEquiv : (B ⊗[F] M)ˣ ≃* ((w : I) → (w.1.Completion ⊗[K] M)ˣ) :=
  (Units.mapEquiv (archimedeanTensorEquiv (B := B) (M := M) v).toMulEquiv).trans MulEquiv.piUnits

/-- Coefficient automorphisms act on every coordinate as the automorphism
of its own right tensor factor. -/
theorem archimedeanTensorUnitsEquiv_action (σ : Gal(M/K)) (x : (B ⊗[F] M)ˣ) (w : I) :
    archimedeanTensorUnitsEquiv v (tensorAction F B M (σ.restrictScalars F) x) w =
      tensorAction K (w.1.Completion) M σ (archimedeanTensorUnitsEquiv v x w) := by
  apply Units.ext
  change archimedeanTensorEquiv v
      (Algebra.TensorProduct.lTensor (S := B) B (σ.restrictScalars F).toAlgHom (x : B ⊗[F] M)) w =
    Algebra.TensorProduct.lTensor (S := w.1.Completion) (w.1.Completion) σ.toAlgHom
      (archimedeanTensorEquiv v (x : B ⊗[F] M) w)
  generalize (x : B ⊗[F] M) = z
  induction z using TensorProduct.inductionOn with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- The image of a global left-factor unit has its completion in each factor. -/
theorem archimedeanTensorUnitsEquiv_left (b : Bˣ) (w : I) :
    archimedeanTensorUnitsEquiv (M := M) v (leftTensorUnit b) w =
      leftTensorUnit (Units.map (algebraMap B (w.1.Completion)).toMonoidHom b) := by
  apply Units.ext
  change archimedeanTensorEquiv v ((b : B) ⊗ₜ[F] (1 : M)) w =
    (algebraMap B (w.1.Completion) (b : B)) ⊗ₜ[K] 1
  rw [archimedeanTensorEquiv_tmul]

/-- The original determinant norm is the product of the determinant norms of the factors. -/
theorem tensorNormUnits_archimedean (x : (B ⊗[F] M)ˣ) :
    tensorNormUnits F B M x =
      ∏ w : I, tensorNormUnits K (w.1.Completion) M (archimedeanTensorUnitsEquiv v x w) := by
  apply Units.ext
  simp only [Units.coe_prod]
  let y := Algebra.TensorProduct.comm F B M (x : B ⊗[F] M)
  let e := archimedeanCompletedTensorEquiv (B := B) (M := M) v
  change Algebra.norm M y = ∏ w : I, Algebra.norm M
    (Algebra.TensorProduct.comm K w.1.Completion M
      (Algebra.TensorProduct.comm K M w.1.Completion ((e y) w)))
  rw [← Algebra.norm_eq_of_algEquiv e, norm_pi]
  apply Finset.prod_congr rfl
  intro w _
  rw [← Algebra.TensorProduct.comm_symm K M w.1.Completion, AlgEquiv.symm_apply_apply]

variable [FiniteDimensional v.Completion M] [IsGalois v.Completion M] [IsAlgClosed M]

/-- A crossed cocycle of archimedean tensor units is the crossed coboundary
of an actual tensor unit. -/
theorem exists_archimedeanTensorCoboundary (c : Gal(M/K) → (B ⊗[F] M)ˣ)
    (hc : ∀ σ τ, c (σ * τ) = tensorAction F B M (σ.restrictScalars F) (c τ) * c σ) :
    ∃ x : (B ⊗[F] M)ˣ, ∀ σ,
      tensorAction F B M (σ.restrictScalars F) x / x = c σ := by
  let e := archimedeanTensorUnitsEquiv (B := B) (M := M) v
  have hv (w : I) : ∃ y : (w.1.Completion ⊗[K] M)ˣ, ∀ σ,
      tensorAction K (w.1.Completion) M σ y / y = e (c σ) w := by
    let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
    let j : w.1.Completion →ₐ[K] M := IsAlgClosed.lift
    let : Algebra (w.1.Completion) M := j.toRingHom.toAlgebra
    let : IsScalarTower K (w.1.Completion) M := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    apply exists_tensorCoboundary
    intro σ τ
    rw [hc σ τ, map_mul]
    change e (tensorAction F B M (σ.restrictScalars F) (c τ)) w * e (c σ) w = _
    rw [archimedeanTensorUnitsEquiv_action]
  choose y hy using hv
  let x := e.symm y
  refine ⟨x, fun σ => e.injective ?_⟩
  funext w
  rw [map_div]
  change archimedeanTensorUnitsEquiv v (tensorAction F B M (σ.restrictScalars F) x) w /
    e x w = e (c σ) w
  rw [archimedeanTensorUnitsEquiv_action, show e x = y from e.apply_symm_apply y]
  exact hy w σ

end Langlands.ClassField.Global.TensorUnitShapiro
