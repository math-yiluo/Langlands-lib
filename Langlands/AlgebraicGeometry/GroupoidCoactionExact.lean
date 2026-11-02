import Langlands.AlgebraicGeometry.GroupoidCoactionUniversal
import Mathlib.RingTheory.Flat.Equalizer

/-! # Kernel coactions and transport -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

lemma lTensor_alg_smul {T : Type u} [CommRing T] [Algebra B T]
    (f : M →ₗ[B] N) (a : T) (x : T ⊗[B] M) :
    LinearMap.lTensor T f (a • x) = a • LinearMap.lTensor T f x :=
  (AlgebraTensorModule.lTensor T T f).map_smul a x

lemma lTensor_rTensor_commute {T : Type u} [CommRing T] [Algebra B T]
    (f : M →ₗ[B] N) (φ : C →ₐ[B] T) (x : C ⊗[B] M) :
    LinearMap.lTensor T f (LinearMap.rTensor M φ.toLinearMap x) =
      LinearMap.rTensor N φ.toLinearMap (LinearMap.lTensor C f x) := by
  induction x <;> simp_all

lemma coactionCompose_map {T : Type u} [CommRing T] [Algebra B T]
    (θM : M →+ C ⊗[B] M) (θN : N →+ C ⊗[B] N)
    (hM : ∀ (b : B) (m : M), θM (b • m) = t b • θM m)
    (hN : ∀ (b : B) (n : N), θN (b • n) = t b • θN n)
    (f : M →ₗ[B] N) (hf : ∀ m : M, θN (f m) = LinearMap.lTensor C f (θM m))
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t) (x : C ⊗[B] M) :
    LinearMap.lTensor T f (coactionCompose t M θM hM φ₁ φ₂ h x) =
      coactionCompose t N θN hN φ₁ φ₂ h (LinearMap.lTensor C f x) := by
  induction x with
  | tmul c m =>
    change LinearMap.lTensor T f
      (φ₁ c • LinearMap.rTensor M φ₂.toLinearMap (θM m)) =
      φ₁ c • LinearMap.rTensor N φ₂.toLinearMap (θN (f m))
    rw [lTensor_alg_smul, lTensor_rTensor_commute, hf m]
  | add x y hx hy => simp [hx, hy]

namespace GroupoidCoaction

/-- The coaction as a semilinear map into its tensor module. -/
def semilinearMap (θ : GroupoidCoaction t M) : M →ₛₗ[t] C ⊗[B] M where
  __ := θ.coaction
  map_smul' := θ.map_smul

/-- Transport a coaction through an injective equivariant linear map. -/
noncomputable def ofInjective (hE : RingEtaleEquivalenceRelation t)
    (θN : GroupoidCoaction t N) (f : M →ₗ[B] N) (hinj : Function.Injective f)
    (θ : M →+ C ⊗[B] M) (hθ : ∀ (b : B) (m : M), θ (b • m) = t b • θ m)
    (hf : ∀ m : M, θN.coaction (f m) = LinearMap.lTensor C f (θ m)) :
    GroupoidCoaction t M := by
  letI := hE.composable_flat
  refine ofUniversal hE θ hθ (fun m => ?_) (fun m => ?_)
  · apply Module.Flat.lTensor_preserves_injective_linearMap f hinj
    rw [lTensor_rTensor_commute, ← hf m,
      θN.counit B hE.identity hE.identity_comp_t]
    simp
  · apply Module.Flat.lTensor_preserves_injective_linearMap f hinj
    rw [lTensor_rTensor_commute, ← hf m,
      θN.coassoc _ _ _ _ _ hE.composableComposite_comp_t, hf m]
    exact (coactionCompose_map θ θN.coaction hθ θN.map_smul f hf _ _ _ (θ m)).symm

/-- Transport a coaction through a surjective equivariant linear map. -/
def ofSurjective (θM : GroupoidCoaction t M) (f : M →ₗ[B] N)
    (hsurj : Function.Surjective f)
    (θ : N →+ C ⊗[B] N) (hθ : ∀ (b : B) (n : N), θ (b • n) = t b • θ n)
    (hf : ∀ m : M, θ (f m) = LinearMap.lTensor C f (θM.coaction m)) :
    GroupoidCoaction t N where
  coaction := θ
  map_smul := hθ
  counit T _ _ φ hφ n := by
    obtain ⟨m, rfl⟩ := hsurj n
    rw [hf, ← lTensor_rTensor_commute, θM.counit T φ hφ]
    simp
  coassoc T _ _ φ₁ φ₂ φ₃ h h₃ n := by
    obtain ⟨m, rfl⟩ := hsurj n
    rw [hf, ← lTensor_rTensor_commute, θM.coassoc T φ₁ φ₂ φ₃ h h₃]
    exact coactionCompose_map θM.coaction θ θM.map_smul hθ f hf φ₁ φ₂ h (θM.coaction m)

section Kernel

variable [Module.Flat B C]
variable (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
variable (f : M →ₗ[B] N) (hf : θM.IsHom θN f)

/-- The kernel's semilinear coaction, using flatness to identify tensor kernels. -/
noncomputable def kernelSemilinearMap : LinearMap.ker f →ₛₗ[t] C ⊗[B] LinearMap.ker f :=
  (LinearMap.tensorKerEquiv C C f).symm.toLinearMap.comp
    ((θM.semilinearMap.domRestrict (LinearMap.ker f)).codRestrict
      (LinearMap.ker (AlgebraTensorModule.lTensor C C f)) (fun m => by
        change LinearMap.lTensor C f (θM.coaction m) = 0
        rw [← hf m, show f m = 0 from m.property, map_zero]))

lemma kernelSemilinearMap_subtype (m : LinearMap.ker f) :
    LinearMap.lTensor C (LinearMap.ker f).subtype (kernelSemilinearMap θM θN f hf m) =
      θM.coaction m :=
  LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm C C f _

end Kernel

/-- The kernel coaction of an equivariant linear map on the affine relation. -/
noncomputable def kernel (hE : RingEtaleEquivalenceRelation t)
    (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) : GroupoidCoaction t (LinearMap.ker f) := by
  letI : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  exact ofInjective hE θM (LinearMap.ker f).subtype (LinearMap.ker f).subtype_injective
    (kernelSemilinearMap θM θN f hf).toAddMonoidHom
    (fun b m => (kernelSemilinearMap θM θN f hf).map_smulₛₗ b m)
    (fun m => (kernelSemilinearMap_subtype θM θN f hf m).symm)

lemma kernel_subtype_isHom (hE : RingEtaleEquivalenceRelation t)
    (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) :
    (kernel hE θM θN f hf).IsHom θM (LinearMap.ker f).subtype := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  intro m
  exact (kernelSemilinearMap_subtype θM θN f hf m).symm

end GroupoidCoaction

end Langlands.AlgebraicGeometry
