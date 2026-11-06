import Langlands.Geometry.Building.AffineRootSystemTransport
import Langlands.Geometry.Building.AffineWeylGroups

/-! # Extended affine Weyl groups under affine equivalences -/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

universe uV uA uW uB

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {W : Type uW} {B : Type uB} [AddCommGroup W] [Module ℝ W] [AddTorsor W B]

/-- The derivative Weyl group is the image of the affine Weyl group under the derivative. -/
theorem map_affineWeylGroup_linearHom (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    (affineWeylGroup Ψ).map AffineEquiv.linearHom = derivativeWeylGroup Ψ := by
  unfold affineWeylGroup derivativeWeylGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext s
  constructor
  · rintro ⟨_, ⟨ψ, hψ, v, hv, rfl⟩, rfl⟩
    exact ⟨ψ, hψ, v, hv, affineReflection_linear ψ hv.1⟩
  · rintro ⟨ψ, hψ, v, hv, rfl⟩
    exact ⟨affineReflection ψ hv.1, ⟨ψ, hψ, v, hv, rfl⟩,
      affineReflection_linear ψ hv.1⟩

/-- Membership of a transported functional reflects membership of the original root set. -/
theorem affineFunctionalTransport_mem_transportedRoots_iff (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (ψ : A →ᵃ[ℝ] ℝ) :
    affineFunctionalTransport e ψ ∈ transportedRoots e Ψ ↔ ψ ∈ Ψ :=
  (affineFunctionalTransport e).injective.mem_set_image

/-- Inverse precomposition commutes with conjugation of affine automorphisms. -/
theorem affineFunctionalTransport_comp_affineConjugation (e : A ≃ᵃ[ℝ] B)
    (ψ : A →ᵃ[ℝ] ℝ) (g : A ≃ᵃ[ℝ] A) :
    (affineFunctionalTransport e ψ).comp (affineConjugation e g).toAffineMap =
      affineFunctionalTransport e (ψ.comp g.toAffineMap) := by
  ext x
  simp only [AffineMap.comp_apply, AffineEquiv.coe_toAffineMap,
    affineFunctionalTransport_apply, affineConjugation_apply, e.symm_apply_apply]

/-- Conjugation preserves and reflects the whole root-stabilizer predicate. -/
theorem mem_rootStabilizer_affineConjugation_iff (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (g : A ≃ᵃ[ℝ] A) :
    affineConjugation e g ∈ rootStabilizer (transportedRoots e Ψ) ↔
      g ∈ rootStabilizer Ψ := by
  rw [mem_rootStabilizer, mem_rootStabilizer]
  constructor
  · intro h ψ
    simpa only [affineFunctionalTransport_comp_affineConjugation,
      affineFunctionalTransport_mem_transportedRoots_iff] using h (affineFunctionalTransport e ψ)
  · intro h φ
    obtain ⟨ψ, rfl⟩ := (affineFunctionalTransport e).surjective φ
    simpa only [affineFunctionalTransport_comp_affineConjugation,
      affineFunctionalTransport_mem_transportedRoots_iff] using h ψ

/-- Conjugation carries every extended affine Weyl element to a transported one. -/
theorem affineConjugation_mem_extendedAffineWeylGroup (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) {g : A ≃ᵃ[ℝ] A}
    (hg : g ∈ extendedAffineWeylGroup Ψ) :
    affineConjugation e g ∈ extendedAffineWeylGroup (transportedRoots e Ψ) := by
  refine ⟨(mem_rootStabilizer_affineConjugation_iff e Ψ g).2 hg.1, ?_⟩
  have hlin := hg.2
  rw [← map_affineWeylGroup_linearHom] at hlin
  obtain ⟨w, hw, hwg⟩ := hlin
  change w.linear = g.linear at hwg
  have hw' : affineConjugation e w ∈ affineWeylGroup (transportedRoots e Ψ) := by
    rw [← map_affineWeylGroup]
    exact ⟨w, hw, rfl⟩
  have heq : (affineConjugation e w).linear = (affineConjugation e g).linear := by
    change (e.linear.symm.trans w.linear).trans e.linear =
      (e.linear.symm.trans g.linear).trans e.linear
    rw [hwg]
  change (affineConjugation e g).linear ∈ derivativeWeylGroup (transportedRoots e Ψ)
  rw [← heq]
  exact linear_mem_derivativeWeylGroup hw'

/-- The transported extended affine Weyl group is the entire conjugate group. -/
theorem map_extendedAffineWeylGroup (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    (extendedAffineWeylGroup Ψ).map (affineConjugation e).toMonoidHom =
      extendedAffineWeylGroup (transportedRoots e Ψ) := by
  ext g
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact affineConjugation_mem_extendedAffineWeylGroup e Ψ hw
  · intro hg
    have hback := affineConjugation_mem_extendedAffineWeylGroup e.symm
      (transportedRoots e Ψ) hg
    rw [transportedRoots_symm] at hback
    refine ⟨affineConjugation e.symm g, hback, ?_⟩
    ext x
    change e (e.symm (g (e (e.symm x)))) = g x
    simp only [e.apply_symm_apply]

/-- Affine conjugation identifies the actual extended affine Weyl subgroups. -/
def extendedAffineWeylTransportEquiv (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    extendedAffineWeylGroup Ψ ≃* extendedAffineWeylGroup (transportedRoots e Ψ) where
  toFun g := ⟨affineConjugation e g.val,
    affineConjugation_mem_extendedAffineWeylGroup e Ψ g.property⟩
  invFun g := ⟨affineConjugation e.symm g.val, by
    simpa only [transportedRoots_symm] using
      affineConjugation_mem_extendedAffineWeylGroup e.symm (transportedRoots e Ψ) g.property⟩
  left_inv g := by
    apply Subtype.ext
    ext x
    change e.symm (e (g.val (e.symm (e x)))) = g.val x
    simp only [e.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    ext x
    change e (e.symm (g.val (e (e.symm x)))) = g.val x
    simp only [e.apply_symm_apply]
  map_mul' g h := Subtype.ext ((affineConjugation e).map_mul g.val h.val)

@[simp] theorem extendedAffineWeylTransportEquiv_apply (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (g : extendedAffineWeylGroup Ψ) :
    (extendedAffineWeylTransportEquiv e Ψ g).val = affineConjugation e g.val := rfl

end Langlands.Geometry.Building.AffineRootSystem
