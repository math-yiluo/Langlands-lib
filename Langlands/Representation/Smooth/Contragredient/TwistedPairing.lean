import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Mathlib.LinearAlgebra.BilinearMap

/-! # Twisted bilinear forms from a smooth-dual equivalence -/

noncomputable section
universe uG uV
set_option autoImplicit false

namespace Langlands.SmoothTwistedPairing

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (θ : G → G) (E : V ≃ₗ[ℂ] SmoothDual ρ)

/-- Evaluate the supplied twisted smooth-dual equivalence in the second argument. -/
def form : V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  ((smoothDualPairing ρ).comp E.toLinearMap).flip

omit [IsTopologicalGroup G] in
@[simp]
theorem form_apply (x y : V) : form ρ E x y = (E y).val x := rfl

variable (hE : ∀ g x, E (ρ (θ g) x) = smoothContragredient ρ g (E x))

include hE in
/-- The smooth-dual covariance gives the corresponding twisted bilinear identity. -/
theorem form_invariant (g : G) (x y : V) :
    form ρ E (ρ g x) (ρ (θ g) y) = form ρ E x y := by
  change (E (ρ (θ g) y)).val (ρ g x) = (E y).val x
  rw [hE]
  change (E y).val (ρ g⁻¹ (ρ g x)) = (E y).val x
  rw [Representation.inv_self_apply]

omit [IsTopologicalGroup G] in
theorem form_ne_zero [Nontrivial V] : form ρ E ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  intro hzero
  have hEx : E x = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    exact congrArg (fun B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ => B y x) hzero
  exact hx (E.injective (hEx.trans (map_zero E).symm))

variable (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hθ : ∀ g ∈ K, θ g ∈ K)
  (e : fixedVectors ρ K.toSubgroup) (he : e ≠ 0)
  (hspan : ∀ w : fixedVectors ρ K.toSubgroup, ∃ c : ℂ, c • e = w)

include hE hρ hK hθ he hspan in
/-- The twisted form does not vanish on the nonzero spherical reference twice. -/
theorem form_reference_ne_zero : form ρ E e.val e.val ≠ 0 := by
  have hfix : ∀ k : K, smoothContragredient ρ k.val (E e.val) = E e.val := by
    intro k
    have h := hE k.val e.val
    have hefix : ρ (θ k.val) e.val = e.val :=
      e.property ⟨θ k.val, hθ k.val k.property⟩
    exact h.symm.trans (congrArg E hefix)
  let ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup := ⟨E e.val, hfix⟩
  intro hzero
  have hres : smoothDualFixedRestriction ρ K.toSubgroup ℓ = 0 := by
    apply LinearMap.ext
    intro w
    obtain ⟨c, rfl⟩ := hspan w
    change (E e.val).val (c • e.val) = 0
    rw [map_smul]
    change c • form ρ E e.val e.val = 0
    rw [hzero, smul_zero]
  have hℓ : ℓ = 0 := (smoothDualFixedRestriction_bijective ρ hρ K hK).1
    (hres.trans (map_zero _).symm)
  have hEx : E e.val = E 0 :=
    (congrArg Subtype.val hℓ).trans (map_zero E).symm
  exact he (Subtype.ext (E.injective hEx))

/-- Rescale the twisted form to have value one on the prescribed spherical reference. -/
def normalizedPairing :
    {B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ //
      (∀ g x y, B (ρ g x) (ρ (θ g) y) = B x y) ∧ B ≠ 0 ∧ B e.val e.val = 1} := by
  have hne := form_reference_ne_zero ρ θ E hE hρ K hK hθ e he hspan
  let B := (form ρ E e.val e.val)⁻¹ • form ρ E
  have hone : B e.val e.val = 1 := by
    exact inv_mul_cancel₀ hne
  refine ⟨B, ?_, ?_, hone⟩
  · intro g x y
    change (form ρ E e.val e.val)⁻¹ • form ρ E (ρ g x) (ρ (θ g) y) =
      (form ρ E e.val e.val)⁻¹ • form ρ E x y
    rw [form_invariant ρ θ E hE]
  · intro hzero
    exact zero_ne_one ((congrArg (fun C : V →ₗ[ℂ] V →ₗ[ℂ] ℂ => C e.val e.val)
      hzero).symm.trans hone)

end Langlands.SmoothTwistedPairing
