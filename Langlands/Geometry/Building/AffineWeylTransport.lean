import Langlands.Geometry.Building.AffineRootSystem
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Transport of affine Weyl groups

An affine equivalence transports affine functionals by inverse precomposition,
coroot vectors by its linear part, and affine automorphisms by conjugation.
These operations identify the affine Weyl groups of the transported root sets.
No affine root system axioms are needed for this comparison.
-/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

open scoped Affine

universe uV uA uW uB

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {W : Type uW} {B : Type uB} [AddCommGroup W] [Module ℝ W] [AddTorsor W B]

/-- Transport affine functionals along an affine equivalence by inverse precomposition. -/
def affineFunctionalTransport (e : A ≃ᵃ[ℝ] B) : (A →ᵃ[ℝ] ℝ) ≃ₗ[ℝ] (B →ᵃ[ℝ] ℝ) :=
  e.arrowCongrₗ (LinearEquiv.refl ℝ ℝ)

@[simp]
theorem affineFunctionalTransport_apply (e : A ≃ᵃ[ℝ] B) (ψ : A →ᵃ[ℝ] ℝ) (x : B) :
    affineFunctionalTransport e ψ x = ψ (e.symm x) :=
  rfl

@[simp]
theorem affineFunctionalTransport_linear_apply (e : A ≃ᵃ[ℝ] B)
    (ψ : A →ᵃ[ℝ] ℝ) (v : V) :
    (affineFunctionalTransport e ψ).linear (e.linear v) = ψ.linear v := by
  change ψ.linear (e.linear.symm (e.linear v)) = ψ.linear v
  rw [LinearEquiv.symm_apply_apply]

/-- The image of a root set under inverse precomposition. -/
def transportedRoots (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Set (B →ᵃ[ℝ] ℝ) :=
  affineFunctionalTransport e '' Ψ

/-- Transport preserves and reflects the coroot condition, including root-set stability. -/
theorem isCoroot_transport_iff (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ))
    (ψ : A →ᵃ[ℝ] ℝ) (v : V) :
    IsCoroot (transportedRoots e Ψ) (affineFunctionalTransport e ψ) (e.linear v) ↔
      IsCoroot Ψ ψ v := by
  constructor
  · intro h
    refine ⟨by simpa using h.1, fun η hη => ?_⟩
    obtain ⟨ζ, hζ, hζeq⟩ := h.2 (affineFunctionalTransport e η) ⟨η, hη, rfl⟩
    have hζeq' : affineFunctionalTransport e ζ =
        affineFunctionalTransport e (η - η.linear v • ψ) := by
      simpa only [map_sub, map_smul, affineFunctionalTransport_linear_apply] using hζeq
    exact (affineFunctionalTransport e).injective hζeq' ▸ hζ
  · intro h
    refine ⟨by simpa using h.1, ?_⟩
    rintro _ ⟨η, hη, rfl⟩
    refine ⟨η - η.linear v • ψ, h.2 η hη, ?_⟩
    simp only [map_sub, map_smul, affineFunctionalTransport_linear_apply]

/-- Conjugation by an affine equivalence is an isomorphism of affine automorphism groups. -/
def affineConjugation (e : A ≃ᵃ[ℝ] B) : (A ≃ᵃ[ℝ] A) ≃* (B ≃ᵃ[ℝ] B) where
  toFun g := (e.symm.trans g).trans e
  invFun g := (e.trans g).trans e.symm
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp]
theorem affineConjugation_apply (e : A ≃ᵃ[ℝ] B) (g : A ≃ᵃ[ℝ] A) (x : B) :
    affineConjugation e g x = e (g (e.symm x)) :=
  rfl

/-- Affine equivalences conjugate root reflections to their transported reflections. -/
theorem affineConjugation_reflection (e : A ≃ᵃ[ℝ] B)
    (ψ : A →ᵃ[ℝ] ℝ) {v : V} (hv : ψ.linear v = 2) :
    affineConjugation e (affineReflection ψ hv) =
      affineReflection (affineFunctionalTransport e ψ)
        (show (affineFunctionalTransport e ψ).linear (e.linear v) = 2 by
          simpa only [affineFunctionalTransport_linear_apply] using hv) := by
  ext x
  simp [AffineEquiv.map_vadd]

/-- The transported affine Weyl group is exactly the conjugate of the original group. -/
theorem map_affineWeylGroup (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    (affineWeylGroup Ψ).map (affineConjugation e).toMonoidHom =
      affineWeylGroup (transportedRoots e Ψ) := by
  unfold affineWeylGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨ψ, hψ, v, hv, rfl⟩, rfl⟩
    refine ⟨affineFunctionalTransport e ψ, ⟨ψ, hψ, rfl⟩, e.linear v,
      (isCoroot_transport_iff e Ψ ψ v).2 hv, ?_⟩
    exact affineConjugation_reflection e ψ hv.1
  · rintro ⟨_, ⟨ψ, hψ, rfl⟩, w, hw, rfl⟩
    let v := e.linear.symm w
    have hv : IsCoroot Ψ ψ v := (isCoroot_transport_iff e Ψ ψ v).1 (by simpa [v] using hw)
    refine ⟨affineReflection ψ hv.1, ⟨ψ, hψ, v, hv, rfl⟩, ?_⟩
    simpa [v] using affineConjugation_reflection e ψ hv.1

/-- A root-set comparison along an affine equivalence yields the Weyl-group comparison. -/
theorem map_affineWeylGroup_of_transportedRoots_eq (e : A ≃ᵃ[ℝ] B)
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Φ : Set (B →ᵃ[ℝ] ℝ)}
    (h : transportedRoots e Ψ = Φ) :
    (affineWeylGroup Ψ).map (affineConjugation e).toMonoidHom = affineWeylGroup Φ := by
  rw [map_affineWeylGroup, h]

end Langlands.Geometry.Building.AffineRootSystem
