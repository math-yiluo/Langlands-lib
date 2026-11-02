import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Group.End
import Mathlib.Data.Rat.Cast.Defs

/-! # Rational spans of subsets of an abelian group and induced automorphisms -/

noncomputable section

open TensorProduct

namespace Langlands.LinearAlgebra.RationalSpan

variable {M : Type*} [AddCommGroup M]

/-- The map `m ↦ 1 ⊗ m` from an abelian group to its rationalization. -/
def toRat : M →+ ℚ ⊗[ℤ] M :=
  (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom

@[simp]
theorem toRat_apply (m : M) : toRat m = (1 : ℚ) ⊗ₜ[ℤ] m :=
  rfl

/-- The `ℚ`-span of the image of `R` in `ℚ ⊗[ℤ] M`. -/
def ratSpan (R : Set M) : Submodule ℚ (ℚ ⊗[ℤ] M) :=
  Submodule.span ℚ (toRat '' R)

theorem toRat_mem_ratSpan {R : Set M} {m : M} (hm : m ∈ R) : toRat m ∈ ratSpan R :=
  Submodule.subset_span (Set.mem_image_of_mem _ hm)

/-- The `ℚ`-linear automorphism `q ⊗ m ↦ q ⊗ e m` of `ℚ ⊗[ℤ] M` induced by an
automorphism `e` of `M`. -/
def ratAut : (M ≃ₗ[ℤ] M) →* ((ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] M)) where
  toFun e := LinearEquiv.baseChange ℤ ℚ M M e
  map_one' := LinearEquiv.toLinearMap_injective <|
    TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl
  map_mul' _ _ := LinearEquiv.toLinearMap_injective <|
    TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl

@[simp]
theorem ratAut_tmul (e : (M ≃ₗ[ℤ] M)) (q : ℚ) (m : M) :
    ratAut e (q ⊗ₜ[ℤ] m) = q ⊗ₜ[ℤ] e m :=
  rfl

theorem ratAut_toRat (e : (M ≃ₗ[ℤ] M)) (m : M) : ratAut e (toRat m) = toRat (e m) :=
  rfl

theorem map_ratSpan (e : (M ≃ₗ[ℤ] M)) (R : Set M) :
    (ratSpan R).map ((ratAut e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] M)) :
      (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] M)) = ratSpan (e '' R) := by
  rw [ratSpan, ratSpan, Submodule.map_span, Set.image_image, Set.image_image]
  rfl

variable {H : Type*} [Group H]

theorem image_eq_of_mapsTo (ρ : H →* (M ≃ₗ[ℤ] M)) {R : Set M}
    (hρ : ∀ h, Set.MapsTo (ρ h) R R) (h : H) : ρ h '' R = R := by
  refine subset_antisymm (hρ h).image_subset fun r hr => ⟨ρ h⁻¹ r, hρ h⁻¹ hr, ?_⟩
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one, id]

/-- A group acting on `M` and preserving `R` acts `ℚ`-linearly on the span of the image of
`R` in `ℚ ⊗[ℤ] M`, by restriction of `ratAut`. -/
def spanAut (ρ : H →* (M ≃ₗ[ℤ] M)) (R : Set M) (hρ : ∀ h, Set.MapsTo (ρ h) R R) :
    H →* (ratSpan R ≃ₗ[ℚ] ratSpan R) where
  toFun h := (ratAut (ρ h)).ofSubmodules (ratSpan R) (ratSpan R) (by
    rw [map_ratSpan, image_eq_of_mapsTo ρ hρ h])
  map_one' := by
    ext x
    simp [LinearEquiv.ofSubmodules_apply]
  map_mul' h₁ h₂ := by
    ext x
    simp [LinearEquiv.ofSubmodules_apply]

@[simp]
theorem coe_spanAut_apply (ρ : H →* (M ≃ₗ[ℤ] M)) (R : Set M) (hρ : ∀ h, Set.MapsTo (ρ h) R R)
    (h : H) (x : ratSpan R) : (spanAut ρ R hρ h x : ℚ ⊗[ℤ] M) = ratAut (ρ h) x :=
  rfl

theorem spanAut_eq_one_of_eq_one (ρ : H →* (M ≃ₗ[ℤ] M)) (R : Set M)
    (hρ : ∀ h, Set.MapsTo (ρ h) R R) {h : H} (h1 : ρ h = 1) : spanAut ρ R hρ h = 1 := by
  ext x
  simp [h1]

/-- For `I` finite, an additive identification `M ≃+ (I → ℤ)` induces
`ℚ ⊗[ℤ] M ≃ₗ[ℚ] (I → ℚ)`. -/
def tensorEquivPi {I : Type*} [Finite I] (e : M ≃+ (I → ℤ)) : ℚ ⊗[ℤ] M ≃ₗ[ℚ] (I → ℚ) :=
  letI := Fintype.ofFinite I
  letI := Classical.decEq I
  (LinearEquiv.baseChange ℤ ℚ M (I → ℤ) e.toIntLinearEquiv).trans
    (TensorProduct.piScalarRight ℤ ℚ ℚ I)

theorem tensorEquivPi_tmul {I : Type*} [Finite I] (e : M ≃+ (I → ℤ)) (q : ℚ) (m : M) :
    tensorEquivPi e (q ⊗ₜ[ℤ] m) = fun j => (e m j : ℚ) * q := by
  ext j
  simp [tensorEquivPi, TensorProduct.piScalarRight_apply, zsmul_eq_mul]

theorem tensorEquivPi_toRat {I : Type*} [Finite I] (e : M ≃+ (I → ℤ)) (m : M) :
    tensorEquivPi e (toRat m) = fun j => (e m j : ℚ) := by
  rw [toRat_apply, tensorEquivPi_tmul]
  simp

theorem toRat_injective {I : Type*} [Finite I] (e : M ≃+ (I → ℤ)) :
    Function.Injective (toRat : M → ℚ ⊗[ℤ] M) := by
  intro m m' h
  have h' := congrArg (tensorEquivPi e) h
  rw [tensorEquivPi_toRat, tensorEquivPi_toRat] at h'
  refine e.injective (funext fun j => ?_)
  exact_mod_cast congrFun h' j

end Langlands.LinearAlgebra.RationalSpan
