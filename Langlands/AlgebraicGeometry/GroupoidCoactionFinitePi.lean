import Langlands.AlgebraicGeometry.GroupoidCoactionExact
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComoduleExactness
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Finite products of coactions -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M : Type v} [AddCommGroup M] [Module B M]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The tensor-product comparison is given coordinatewise by tensoring projections. -/
lemma piRight_apply_eq_lTensor {T : Type u} [CommRing T] [Algebra B T]
    (x : T ⊗[B] (ι → M)) (i : ι) :
    piRight B T T (fun _ : ι => M) x i =
      LinearMap.lTensor T (LinearMap.proj i) x := by
  induction x with
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Two tensors with a finite product are equal when all their projections agree. -/
lemma finitePi_tensor_ext {T : Type u} [CommRing T] [Algebra B T]
    {x y : T ⊗[B] (ι → M)}
    (h : ∀ i : ι, LinearMap.lTensor T (LinearMap.proj i) x =
      LinearMap.lTensor T (LinearMap.proj i) y) : x = y := by
  apply (piRight B T T (fun _ : ι => M)).injective
  ext i
  simpa only [piRight_apply_eq_lTensor] using h i

/-- The additive coaction on a finite product, obtained from its coordinates. -/
noncomputable def finitePiCoactionMap (θ : GroupoidCoaction t M) :
    (ι → M) →+ C ⊗[B] (ι → M) :=
  (piRight B C C (fun _ : ι => M)).symm.toLinearMap.toAddMonoidHom.comp
    { toFun := fun m i => θ.coaction (m i)
      map_zero' := by ext i; exact map_zero θ.coaction
      map_add' := by intro m n; ext i; exact map_add θ.coaction (m i) (n i) }

@[simp]
lemma finitePiCoactionMap_proj (θ : GroupoidCoaction t M) (m : ι → M) (i : ι) :
    LinearMap.lTensor C (LinearMap.proj i) (finitePiCoactionMap θ m) =
      θ.coaction (m i) := by
  rw [← piRight_apply_eq_lTensor]
  exact congrFun ((piRight B C C (fun _ : ι => M)).apply_symm_apply _) i

lemma finitePiCoactionMap_smul (θ : GroupoidCoaction t M) (b : B) (m : ι → M) :
    finitePiCoactionMap θ (b • m) = t b • finitePiCoactionMap θ m := by
  apply finitePi_tensor_ext
  intro i
  rw [lTensor_alg_smul, finitePiCoactionMap_proj, finitePiCoactionMap_proj]
  exact θ.map_smul b (m i)

/-- The finite product of a coaction with itself. -/
noncomputable def finitePi (θ : GroupoidCoaction t M) : GroupoidCoaction t (ι → M) where
  coaction := finitePiCoactionMap θ
  map_smul := finitePiCoactionMap_smul θ
  counit T _ _ φ hφ m := by
    apply finitePi_tensor_ext
    intro i
    rw [lTensor_rTensor_commute, finitePiCoactionMap_proj, θ.counit T φ hφ]
    rfl
  coassoc T _ _ φ₁ φ₂ φ₃ h h₃ m := by
    apply finitePi_tensor_ext
    intro i
    rw [lTensor_rTensor_commute, finitePiCoactionMap_proj]
    rw [coactionCompose_map (finitePiCoactionMap θ) θ.coaction
      (finitePiCoactionMap_smul θ) θ.map_smul (LinearMap.proj i)
      (fun m => (finitePiCoactionMap_proj θ m i).symm)]
    rw [finitePiCoactionMap_proj]
    exact θ.coassoc T φ₁ φ₂ φ₃ h h₃ (m i)

@[simp]
lemma finitePi_coaction (θ : GroupoidCoaction t M) (m : ι → M) :
    (finitePi θ).coaction m = finitePiCoactionMap θ m := rfl

/-- Coordinate projections are morphisms of coactions. -/
lemma finitePi_proj_isHom (θ : GroupoidCoaction t M) (i : ι) :
    (finitePi (ι := ι) θ).IsHom θ (LinearMap.proj i) :=
  fun m => (finitePiCoactionMap_proj θ m i).symm

/-- The constant-family diagonal is a morphism of coactions. -/
lemma finitePi_diagonal_isHom (θ : GroupoidCoaction t M) :
    θ.IsHom (finitePi θ) (LinearMap.pi (fun _ : ι => LinearMap.id)) := by
  intro m
  apply finitePi_tensor_ext
  intro i
  rw [finitePi_coaction, finitePiCoactionMap_proj, ← LinearMap.lTensor_comp_apply]
  simp

/-- A coefficient coaction is a retract of any nonempty finite product of itself. -/
theorem oneCohomologyVanishes_of_finitePi (θ : GroupoidCoaction t M) (i : ι)
    (hvan : (finitePi (ι := ι) θ).OneCohomologyVanishes) :
    θ.OneCohomologyVanishes := by
  apply oneCohomologyVanishes_of_retract
    (LinearMap.pi (fun _ : ι => LinearMap.id)) (LinearMap.proj i)
    (finitePi_diagonal_isHom θ) (finitePi_proj_isHom θ i) _ hvan
  ext m
  rfl

end Langlands.AlgebraicGeometry.GroupoidCoaction
