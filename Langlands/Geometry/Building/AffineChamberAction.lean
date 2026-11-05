import Langlands.Geometry.Building.AffineChamberSeparation
import Mathlib.GroupTheory.GroupAction.Defs

/-! # The actual affine action on chambers and transport of coroot reflections -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type uV} {A : Type uA}
variable [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- The existing chamber subsets, bundled with their chamber property. -/
def Chambers (Ψ : Set (A →ᵃ[ℝ] ℝ)) := {C : Set A // IsChamber Ψ C}

instance : MulAction (rootStabilizer Ψ) (Chambers Ψ) where
  smul e C := ⟨(e : A ≃ᵃ[ℝ] A) '' C.val,
    C.property.image e.property⟩
  one_smul C := by
    apply Subtype.ext
    exact Set.image_id _
  mul_smul e f C := by
    apply Subtype.ext
    change ((e : A ≃ᵃ[ℝ] A) * (f : A ≃ᵃ[ℝ] A)) '' C.val =
      (e : A ≃ᵃ[ℝ] A) '' ((f : A ≃ᵃ[ℝ] A) '' C.val)
    rw [AffineEquiv.coe_mul, Set.image_image]
    rfl

/-- The bundled action is literally the actual image of the chamber subset. -/
@[simp] theorem Chambers.coe_smul (e : rootStabilizer Ψ) (C : Chambers Ψ) :
    (e • C).val = (e : A ≃ᵃ[ℝ] A) '' C.val :=
  rfl

/-- Transport a coroot by the linear part of a root-preserving automorphism. -/
theorem IsCoroot.map {ψ : A →ᵃ[ℝ] ℝ} {v : V} (hv : IsCoroot Ψ ψ v)
    {e : A ≃ᵃ[ℝ] A} (he : e ∈ rootStabilizer Ψ) :
    IsCoroot Ψ (ψ.comp (e.symm : A →ᵃ[ℝ] A)) (e.linear v) := by
  constructor
  · change ψ.linear (e.linear.symm (e.linear v)) = 2
    simpa only [LinearEquiv.symm_apply_apply] using hv.1
  · intro η hη
    apply (comp_mem_iff he _).1
    have h := hv.2 (η.comp (e : A →ᵃ[ℝ] A)) ((comp_mem_iff he η).2 hη)
    convert h using 1
    ext x
    simp only [AffineMap.comp_apply, AffineMap.coe_sub, Pi.sub_apply,
      AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul,
      AffineEquiv.coe_toAffineMap, AffineEquiv.symm_apply_apply]
    rfl

/-- Actual affine conjugation transports the defining root and coroot. -/
theorem conjugate_affineReflection (e : A ≃ᵃ[ℝ] A)
    (ψ : A →ᵃ[ℝ] ℝ) {v : V} (hv : ψ.linear v = 2) :
    e * affineReflection ψ hv * e⁻¹ =
      affineReflection (ψ.comp (e.symm : A →ᵃ[ℝ] A))
        (show (ψ.comp (e.symm : A →ᵃ[ℝ] A)).linear (e.linear v) = 2 by
          change ψ.linear (e.linear.symm (e.linear v)) = 2
          simpa only [LinearEquiv.symm_apply_apply] using hv) := by
  ext x
  change e ((-ψ (e.symm x)) • v +ᵥ e.symm x) =
    (-ψ (e.symm x)) • e.linear v +ᵥ x
  rw [AffineEquiv.map_vadd, map_smul, AffineEquiv.apply_symm_apply]

end Langlands.Geometry.Building.AffineRootSystem
