import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodule
import Mathlib.RingTheory.Flat.Basic

/-! # Cobar cocycles and invariant lifting

Cocycles are tested over flat algebras. Vanishing for these cocycles is a sufficient
criterion for the published `GroupoidCoaction.IsAcyclic` predicate.
-/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

/-- The degree-zero coboundary `m ↦ θ m - 1 ⊗ m`. -/
def coboundary (θ : GroupoidCoaction t M) : M →+ C ⊗[B] M :=
  θ.coaction - (TensorProduct.mk B C M 1).toAddMonoidHom

@[simp] theorem coboundary_apply (θ : GroupoidCoaction t M) (m : M) :
    θ.coboundary m = θ.coaction m - (1 : C) ⊗ₜ[B] m := rfl

/-- The additive one-cocycle equation at every composable point valued in a flat
`B`-algebra. The `B`-algebra structure is that of the final source point. -/
def IsOneCocycle (θ : GroupoidCoaction t M) (x : C ⊗[B] M) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra B T] [Module.Flat B T]
    (φ₁ : C →+* T) (φ₂ φ₃ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t),
    (φ₃ : C →+* T).comp t = φ₁.comp t →
      LinearMap.rTensor M φ₃.toLinearMap x =
        LinearMap.rTensor M φ₂.toLinearMap x +
          coactionCompose t M θ.coaction θ.map_smul φ₁ φ₂ h x

/-- Every cocycle tested over flat algebras is a degree-zero coboundary. -/
def OneCohomologyVanishes (θ : GroupoidCoaction t M) : Prop :=
  ∀ x : C ⊗[B] M, θ.IsOneCocycle x → ∃ m : M, θ.coboundary m = x

variable {T : Type u} [CommRing T] [Algebra B T]

@[simp] theorem coactionCompose_tmul (θ : GroupoidCoaction t M)
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t) (c : C) (m : M) :
    coactionCompose t M θ.coaction θ.map_smul φ₁ φ₂ h (c ⊗ₜ[B] m) =
      φ₁ c • LinearMap.rTensor M φ₂.toLinearMap (θ.coaction m) := by
  rfl

/-- Pullback on ring coefficients commutes with a linear map on module coefficients. -/
theorem tensor_naturality (f : M →ₗ[B] N) (φ : C →ₐ[B] T) (x : C ⊗[B] M) :
    LinearMap.rTensor N φ.toLinearMap (LinearMap.lTensor C f x) =
      LinearMap.lTensor T f (LinearMap.rTensor M φ.toLinearMap x) := by
  induction x with
  | tmul c m => simp
  | add x y hx hy => simp [hx, hy]

/-- A tensor extension of a linear map commutes with multiplication by the left factor. -/
theorem lTensor_smul (f : M →ₗ[B] N) (a : T) (x : T ⊗[B] M) :
    LinearMap.lTensor T f (a • x) = a • LinearMap.lTensor T f x := by
  induction x with
  | tmul c m => simp [smul_tmul']
  | add x y hx hy => simp [smul_add, hx, hy]

/-- A morphism of coactions intertwines the pointwise composite maps. -/
theorem coactionCompose_naturality {θM : GroupoidCoaction t M}
    {θN : GroupoidCoaction t N} (f : M →ₗ[B] N) (hf : θM.IsHom θN f)
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t) (x : C ⊗[B] M) :
    coactionCompose t N θN.coaction θN.map_smul φ₁ φ₂ h (LinearMap.lTensor C f x) =
      LinearMap.lTensor T f (coactionCompose t M θM.coaction θM.map_smul φ₁ φ₂ h x) := by
  induction x with
  | tmul c m =>
      simp only [LinearMap.lTensor_tmul, coactionCompose_tmul, hf m, tensor_naturality,
        lTensor_smul]
  | add x y hx hy => simp [hx, hy]

/-- Coboundaries satisfy the cocycle equation. -/
theorem isOneCocycle_coboundary (θ : GroupoidCoaction t M) (m : M) :
    θ.IsOneCocycle (θ.coboundary m) := by
  intro T _ _ _ φ₁ φ₂ φ₃ h h₃
  simp only [coboundary_apply, map_sub, LinearMap.rTensor_tmul, map_one,
    coactionCompose_tmul, one_smul, AlgHom.toLinearMap_apply, map_one]
  rw [θ.coassoc T φ₁ φ₂ φ₃ h h₃]
  abel

/-- Coboundaries commute with morphisms of coactions. -/
theorem coboundary_naturality {θM : GroupoidCoaction t M} {θN : GroupoidCoaction t N}
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) (m : M) :
    θN.coboundary (f m) = LinearMap.lTensor C f (θM.coboundary m) := by
  simp [coboundary_apply, hf m]

/-- An injective morphism reflects the cocycle condition, because its scalar extensions
at the test rings are injective by flatness. -/
theorem isOneCocycle_of_injective {θM : GroupoidCoaction t M}
    {θN : GroupoidCoaction t N} (f : M →ₗ[B] N) (hf : θM.IsHom θN f)
    (hinj : Function.Injective f) (x : C ⊗[B] M)
    (hx : θN.IsOneCocycle (LinearMap.lTensor C f x)) : θM.IsOneCocycle x := by
  intro T _ _ _ φ₁ φ₂ φ₃ h h₃
  apply Module.Flat.lTensor_preserves_injective_linearMap f hinj
  simpa only [map_add, ← tensor_naturality, ← coactionCompose_naturality f hf] using
    hx T φ₁ φ₂ φ₃ h h₃

/-- With a flat source algebra, vanishing of these cocycles implies the published
invariant-lifting property `IsAcyclic`. -/
theorem isAcyclic_of_oneCohomologyVanishes [Module.Flat B C]
    (θ : GroupoidCoaction t M) (hθ : θ.OneCohomologyVanishes) : θ.IsAcyclic := by
  intro G Q _ _ _ _ θG θQ i p hi hp hinj hsurj hex q hq
  obtain ⟨g, hg⟩ := hsurj q
  have hzero : LinearMap.lTensor C p (θG.coboundary g) = 0 := by
    rw [← coboundary_naturality p hp, hg]
    change θQ.coaction q - (1 : C) ⊗ₜ[B] q = 0
    exact sub_eq_zero.mpr hq
  have htex := Module.Flat.lTensor_exact C (LinearMap.exact_iff.mpr hex.symm)
  obtain ⟨x, hx⟩ := (htex (θG.coboundary g)).mp hzero
  have hc : θ.IsOneCocycle x :=
    isOneCocycle_of_injective i hi hinj x (hx.symm ▸ isOneCocycle_coboundary θG g)
  obtain ⟨m, hm⟩ := hθ x hc
  have hgm : θG.coboundary g = θG.coboundary (i m) := by
    rw [coboundary_naturality i hi, hm, hx]
  refine ⟨g - i m, ?_, ?_⟩
  · change θG.coaction (g - i m) = (1 : C) ⊗ₜ[B] (g - i m)
    have hz : θG.coboundary (g - i m) = 0 := by
      rw [map_sub, hgm, sub_self]
    exact sub_eq_zero.mp hz
  · have hpi : p (i m) = 0 := by
      have hmem : i m ∈ LinearMap.ker p := by
        rw [← hex]
        exact ⟨m, rfl⟩
      exact hmem
    simp [hg, hpi]

end Langlands.AlgebraicGeometry.GroupoidCoaction
