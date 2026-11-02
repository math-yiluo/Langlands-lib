import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCobar
import Langlands.AlgebraicGeometry.GroupoidCoactionUniversal

/-! # Universal testing and normalization of groupoid cocycles -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

open RingEtaleEquivalenceRelation

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M : Type v} [AddCommGroup M] [Module B M]

/-- The cocycle equation at the universal composable point. -/
def IsUniversalOneCocycle (θ : GroupoidCoaction t M)
    (hE : RingEtaleEquivalenceRelation t) (x : C ⊗[B] M) : Prop :=
  LinearMap.rTensor M hE.composableComposite.toLinearMap x =
    LinearMap.rTensor M (composableSecond t).toLinearMap x +
      coactionCompose t M θ.coaction θ.map_smul (composableFirst t)
        (composableSecond t) (composable_compat t) x

/-- The flat-test cocycle condition is equivalent to its single universal equation. -/
theorem isOneCocycle_iff_universal (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (x : C ⊗[B] M) :
    θ.IsOneCocycle x ↔ θ.IsUniversalOneCocycle hE x := by
  constructor
  · intro hx
    let := hE.composable_flat
    exact hx (composableRing t) (composableFirst t) (composableSecond t)
      hE.composableComposite (composable_compat t) hE.composableComposite_comp_t
  · intro hx T _ _ _ φ₁ φ₂ φ₃ h h₃
    have he := congrArg (LinearMap.rTensor M (composableLift φ₁ φ₂ h).toLinearMap) hx
    simpa only [map_add, rTensor_algHom_comp, hE.composableComposite_factor φ₁ φ₂ φ₃ h h₃,
      composableLift_second,
      Langlands.AlgebraicGeometry.coactionCompose_naturality θ.coaction θ.map_smul
        (composableLift φ₁ φ₂ h) (composableFirst t) (composableSecond t)
        φ₁ φ₂ (composable_compat t) h (composableLift_first φ₁ φ₂ h)
        (composableLift_second φ₁ φ₂ h)] using he

/-- A flat-test cocycle satisfies its equation at arbitrary ring-valued points. -/
theorem IsOneCocycle.specialize {θ : GroupoidCoaction t M} {x : C ⊗[B] M}
    (hx : θ.IsOneCocycle x) (hE : RingEtaleEquivalenceRelation t)
    {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ φ₃ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t)
    (h₃ : (φ₃ : C →+* T).comp t = φ₁.comp t) :
    LinearMap.rTensor M φ₃.toLinearMap x =
      LinearMap.rTensor M φ₂.toLinearMap x +
        coactionCompose t M θ.coaction θ.map_smul φ₁ φ₂ h x := by
  have he := congrArg (LinearMap.rTensor M (composableLift φ₁ φ₂ h).toLinearMap)
    ((isOneCocycle_iff_universal hE θ x).mp hx)
  simpa only [map_add, rTensor_algHom_comp, hE.composableComposite_factor φ₁ φ₂ φ₃ h h₃,
    composableLift_second,
    Langlands.AlgebraicGeometry.coactionCompose_naturality θ.coaction θ.map_smul
      (composableLift φ₁ φ₂ h) (composableFirst t) (composableSecond t)
      φ₁ φ₂ (composable_compat t) h (composableLift_first φ₁ φ₂ h)
      (composableLift_second φ₁ φ₂ h)] using he

/-- A flat-test cocycle vanishes on the identity point. -/
theorem IsOneCocycle.identity_eq_zero {θ : GroupoidCoaction t M} {x : C ⊗[B] M}
    (hx : θ.IsOneCocycle x) (hE : RingEtaleEquivalenceRelation t) :
    LinearMap.rTensor M hE.identity.toLinearMap x = 0 := by
  have h : (hE.identity : C →+* B).comp (algebraMap B C) =
      (hE.identity : C →+* B).comp t := by
    rw [hE.identity_comp_t]
    ext b
    exact hE.identity.commutes b
  have hc (y : C ⊗[B] M) :
      coactionCompose t M θ.coaction θ.map_smul hE.identity hE.identity h y =
        LinearMap.rTensor M hE.identity.toLinearMap y := by
    induction y with
    | tmul c m =>
      simp only [coactionCompose_tmul, θ.counit B hE.identity hE.identity_comp_t,
        LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      simp [smul_tmul', smul_eq_mul]
    | add y z hy hz => simp [hy, hz]
  have he := hx.specialize hE hE.identity hE.identity hE.identity h rfl
  rw [hc] at he
  exact add_eq_left.mp he.symm

end Langlands.AlgebraicGeometry.GroupoidCoaction
