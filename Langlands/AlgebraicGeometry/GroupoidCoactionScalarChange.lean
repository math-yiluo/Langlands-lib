import Langlands.AlgebraicGeometry.GroupoidCoactionUniversal
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Changing a groupoid coaction along a surjective scalar map -/

universe u v

open TensorProduct

set_option linter.unusedSectionVars false

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B S C D : Type u}
  [CommRing B] [CommRing S] [CommRing C] [CommRing D]
  [Algebra B S] [Algebra B C] [Algebra B D] [Algebra S D] [IsScalarTower B S D]
variable {M : Type v} [AddCommGroup M] [Module B M] [Module S M]
  [IsScalarTower B S M]

/-- The natural tensor map when both the coefficient ring and the tensor base
are changed. -/
def scalarChangeTensor (f : C →ₐ[B] D) : C ⊗[B] M →+ D ⊗[S] M :=
  TensorProduct.liftAddHom
    { toFun := fun c =>
        { toFun := fun m => f c ⊗ₜ[S] m
          map_zero' := by simp
          map_add' := fun _ _ => by simp [tmul_add] }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_tmul] }
    (fun b c m => by
      change f (b • c) ⊗ₜ[S] m = f c ⊗ₜ[S] (b • m)
      have hf : f (b • c) = b • f c := f.toLinearMap.map_smul b c
      rw [hf]
      exact TensorProduct.smul_tmul b (f c) m)

@[simp]
lemma scalarChangeTensor_tmul (f : C →ₐ[B] D) (c : C) (m : M) :
    scalarChangeTensor (S := S) f (c ⊗ₜ[B] m) = f c ⊗ₜ[S] m :=
  rfl

lemma scalarChangeTensor_smul (f : C →ₐ[B] D) (c : C) (x : C ⊗[B] M) :
    scalarChangeTensor (S := S) f (c • x) =
      f c • scalarChangeTensor (S := S) f x := by
  induction x with
  | tmul d m => simp [smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

lemma scalarChangeTensor_rTensor {T : Type u} [CommRing T]
    [Algebra S T] [Algebra B T] [IsScalarTower B S T]
    (f : C →ₐ[B] D) (φ : D →ₐ[S] T)
    (x : C ⊗[B] M) :
    scalarChangeTensor (S := S) (AlgHom.id B T)
      (LinearMap.rTensor M ((φ.restrictScalars B).comp f).toLinearMap x) =
    LinearMap.rTensor M φ.toLinearMap (scalarChangeTensor (S := S) f x) := by
  induction x with
  | tmul c m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {t : B →+* C} {τ : S →+* D}

/-- Compatibility of the target maps after changing scalars. -/
lemma scalarChange_target_apply (f : C →ₐ[B] D)
    (hτ : τ.comp (algebraMap B S) = f.toRingHom.comp t) (b : B) :
    τ (algebraMap B S b) = f (t b) :=
  congrArg (fun g : B →+* D => g b) hτ

lemma scalarChange_map_smul (θ : GroupoidCoaction t M)
    (f : C →ₐ[B] D) (hS : Function.Surjective (algebraMap B S))
    (hτ : τ.comp (algebraMap B S) = f.toRingHom.comp t) (s : S) (m : M) :
    scalarChangeTensor (S := S) f (θ.coaction (s • m)) =
      τ s • scalarChangeTensor (S := S) f (θ.coaction m) := by
  obtain ⟨b, rfl⟩ := hS s
  rw [IsScalarTower.algebraMap_smul S, θ.map_smul, scalarChangeTensor_smul,
    scalarChange_target_apply f hτ]

lemma scalarChangeTensor_coactionCompose (θ : GroupoidCoaction t M)
    {T : Type u} [CommRing T] [Algebra S T] [Algebra B T] [IsScalarTower B S T]
    (f : C →ₐ[B] D) (hS : Function.Surjective (algebraMap B S))
    (hτ : τ.comp (algebraMap B S) = f.toRingHom.comp t)
    (φ₁ : D →+* T) (φ₂ : D →ₐ[S] T)
    (h : φ₁.comp (algebraMap S D) = φ₂.toRingHom.comp τ)
    (hB : (φ₁.comp f.toRingHom).comp (algebraMap B C) =
      ((φ₂.restrictScalars B).comp f).toRingHom.comp t)
    (x : C ⊗[B] M) :
    scalarChangeTensor (S := S) (AlgHom.id B T)
      (coactionCompose t M θ.coaction θ.map_smul (φ₁.comp f.toRingHom)
        ((φ₂.restrictScalars B).comp f) hB x) =
    coactionCompose τ M ((scalarChangeTensor (S := S) f).comp θ.coaction)
      (scalarChange_map_smul θ f hS hτ) φ₁ φ₂ h
      (scalarChangeTensor (S := S) f x) := by
  induction x with
  | tmul c m =>
    change scalarChangeTensor (S := S) (AlgHom.id B T)
      (φ₁ (f c) • LinearMap.rTensor M ((φ₂.restrictScalars B).comp f).toLinearMap
        (θ.coaction m)) =
      φ₁ (f c) • LinearMap.rTensor M φ₂.toLinearMap
        (scalarChangeTensor (S := S) f (θ.coaction m))
    rw [scalarChangeTensor_smul, scalarChangeTensor_rTensor]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A coaction transported along a surjective scalar map and a compatible
map of relation rings. -/
def scalarChange (θ : GroupoidCoaction t M)
    (f : C →ₐ[B] D) (hS : Function.Surjective (algebraMap B S))
    (hτ : τ.comp (algebraMap B S) = f.toRingHom.comp t) :
    GroupoidCoaction τ M where
  coaction := (scalarChangeTensor (S := S) f).comp θ.coaction
  map_smul := scalarChange_map_smul θ f hS hτ
  counit T _ _ φ hφ m := by
    let : Algebra B T := ((algebraMap S T).comp (algebraMap B S)).toAlgebra
    let : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hB : ((φ.restrictScalars B).comp f).toRingHom.comp t =
        algebraMap B T := by
      ext b
      change φ (f (t b)) = algebraMap S T (algebraMap B S b)
      rw [← scalarChange_target_apply f hτ]
      exact congrArg (fun q : S →+* T => q (algebraMap B S b)) hφ
    change LinearMap.rTensor M φ.toLinearMap
      (scalarChangeTensor (S := S) f (θ.coaction m)) = _
    rw [← scalarChangeTensor_rTensor]
    have hunit := θ.counit T ((φ.restrictScalars B).comp f) hB m
    rw [hunit]
    simp
  coassoc T _ _ φ₁ φ₂ φ₃ h h₃ m := by
    let : Algebra B T := ((algebraMap S T).comp (algebraMap B S)).toAlgebra
    let : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hB : (φ₁.comp f.toRingHom).comp (algebraMap B C) =
        ((φ₂.restrictScalars B).comp f).toRingHom.comp t := by
      ext b
      change φ₁ (f (algebraMap B C b)) = φ₂ (f (t b))
      rw [f.commutes, IsScalarTower.algebraMap_apply B S D,
        ← scalarChange_target_apply f hτ]
      exact congrArg (fun q : S →+* T => q (algebraMap B S b)) h
    have hB₃ : ((φ₃.restrictScalars B).comp f).toRingHom.comp t =
        (φ₁.comp f.toRingHom).comp t := by
      ext b
      change φ₃ (f (t b)) = φ₁ (f (t b))
      rw [← scalarChange_target_apply f hτ]
      exact congrArg (fun q : S →+* T => q (algebraMap B S b)) h₃
    change LinearMap.rTensor M φ₃.toLinearMap
      (scalarChangeTensor (S := S) f (θ.coaction m)) = _
    rw [← scalarChangeTensor_rTensor,
      θ.coassoc T (φ₁.comp f.toRingHom) ((φ₂.restrictScalars B).comp f)
        ((φ₃.restrictScalars B).comp f) hB hB₃,
      scalarChangeTensor_coactionCompose θ f hS hτ φ₁ φ₂ h hB]
    rfl

@[simp]
lemma scalarChange_coaction (θ : GroupoidCoaction t M)
    (f : C →ₐ[B] D) (hS : Function.Surjective (algebraMap B S))
    (hτ : τ.comp (algebraMap B S) = f.toRingHom.comp t) (m : M) :
    (scalarChange θ f hS hτ).coaction m =
      scalarChangeTensor (S := S) f (θ.coaction m) := rfl

lemma scalarChange_mem_invariants_iff (θ : GroupoidCoaction t M)
    (f : C →ₐ[B] D) (hS : Function.Surjective (algebraMap B S))
    (hτ : τ.comp (algebraMap B S) = f.toRingHom.comp t)
    (hinj : Function.Injective (scalarChangeTensor (M := M) (S := S) f)) (m : M) :
    m ∈ (scalarChange θ f hS hτ).invariants ↔ m ∈ θ.invariants := by
  change scalarChangeTensor (S := S) f (θ.coaction m) = (1 : D) ⊗ₜ[S] m ↔
    θ.coaction m = (1 : C) ⊗ₜ[B] m
  rw [← map_one f, ← scalarChangeTensor_tmul]
  exact hinj.eq_iff

end Langlands.AlgebraicGeometry.GroupoidCoaction
