import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Fixed bases of semilinear Galois lines -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v

namespace Langlands.LinearAlgebra.GaloisLineDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L]

/-- The subgroup/fixed-field Galois equivalence preserves the action on coefficients. -/
@[simp] theorem subgroupEquivAlgEquiv_apply (H : Subgroup (L ≃ₐ[k] L))
    (σ : H) (x : L) :
    IntermediateField.subgroupEquivAlgEquiv H σ x = σ.val x := rfl

/-- Hilbert 90 for an arbitrary subgroup of the automorphisms of a finite extension. -/
theorem exists_coboundary (H : Subgroup (L ≃ₐ[k] L)) (c : H → Lˣ)
    (hc : ∀ σ τ : H, (c (σ * τ) : L) = σ.val (c τ : L) * (c σ : L)) :
    ∃ b : Lˣ, ∀ σ : H, σ.val (b : L) / (b : L) = (c σ : L) := by
  let E := IntermediateField.fixedField H
  let e := IntermediateField.subgroupEquivAlgEquiv H
  let d : (L ≃ₐ[E] L) → Lˣ := fun σ => c (e.symm σ)
  have he (σ : L ≃ₐ[E] L) (x : L) : (e.symm σ).val x = σ x := by
    rw [← subgroupEquivAlgEquiv_apply, e.apply_symm_apply]
  have hd : groupCohomology.IsMulCocycle₁ d := by
    intro σ τ
    apply Units.ext
    change (c (e.symm (σ * τ)) : L) = σ (c (e.symm τ) : L) * (c (e.symm σ) : L)
    rw [map_mul, hc, he]
  obtain ⟨b, hb⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units d hd
  refine ⟨b, fun σ => ?_⟩
  have h := congrArg (fun z : Lˣ => (z : L)) (hb (e σ))
  simpa only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_coe, d, e.symm_apply_apply, e, subgroupEquivAlgEquiv_apply] using h

variable (H : Subgroup (L ≃ₐ[k] L))
  {V : Type v} [AddCommGroup V] [Module L V]
  [DistribMulAction H V] [SMulDistribClass H L V]

/-- A finite-extension semilinear line has a nonzero vector fixed by the whole subgroup. -/
theorem exists_fixed_nonzero (hV : Module.finrank L V = 1) :
    ∃ b : V, b ≠ 0 ∧ ∀ σ : H, σ • b = b := by
  classical
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hV
  let v := e (1 : L)
  have hv : v ≠ 0 := by
    exact e.map_eq_zero_iff.not.mpr one_ne_zero
  let c : H → Lˣ := fun σ => Units.mk0 (e.symm (σ • v)) (by
    intro hz
    have hσv : σ • v = 0 := e.symm.map_eq_zero_iff.mp hz
    exact hv ((smul_eq_zero_iff_eq σ).mp hσv))
  have hcv (σ : H) : (c σ : L) • v = σ • v := by
    change e.symm (σ • v) • e 1 = σ • v
    rw [← e.map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]
  have hc (σ τ : H) : (c (σ * τ) : L) = σ.val (c τ : L) * (c σ : L) := by
    apply (smul_left_injective L hv)
    change (c (σ * τ) : L) • v = (σ.val (c τ : L) * (c σ : L)) • v
    rw [hcv, mul_smul, ← hcv τ, smul_distrib_smul, ← hcv σ, mul_smul]
    rfl
  obtain ⟨d, hd⟩ := exists_coboundary H c hc
  refine ⟨(d : L)⁻¹ • v, smul_ne_zero (inv_ne_zero d.ne_zero) hv, fun σ => ?_⟩
  rw [smul_distrib_smul]
  change σ.val ((d : L)⁻¹) • (σ • v) = _
  rw [map_inv₀, ← hcv σ, ← mul_smul, ← hd σ]
  congr 1
  field_simp

/-- Choosing a fixed nonzero basis gives coordinates with the ordinary coefficient action. -/
theorem exists_equivariant_linearEquiv (hV : Module.finrank L V = 1) :
    ∃ e : L ≃ₗ[L] V, ∀ (σ : H) (x : L), σ • e x = e (σ.val x) := by
  obtain ⟨b, hb, hfixed⟩ := exists_fixed_nonzero H hV
  let f : L →ₗ[L] V := (LinearMap.id : L →ₗ[L] L).smulRight b
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact (smul_left_injective L hb) hxy
    · intro y
      exact exists_smul_eq_of_finrank_eq_one hV hb y
  refine ⟨LinearEquiv.ofBijective f hf, fun σ x => ?_⟩
  change σ • (x • b) = (σ.val x) • b
  rw [smul_distrib_smul, hfixed]
  rfl

/-- A chosen equivariant linear coordinate on the semilinear line. -/
def equivariantLinearEquiv (hV : Module.finrank L V = 1) : L ≃ₗ[L] V :=
  Classical.choose (exists_equivariant_linearEquiv H hV)

/-- The chosen coordinate intertwines the subgroup action with its coefficient action. -/
theorem equivariantLinearEquiv_smul (hV : Module.finrank L V = 1)
    (σ : H) (x : L) :
    σ • equivariantLinearEquiv H hV x = equivariantLinearEquiv H hV (σ.val x) :=
  Classical.choose_spec (exists_equivariant_linearEquiv H hV) σ x

end Langlands.LinearAlgebra.GaloisLineDescent
