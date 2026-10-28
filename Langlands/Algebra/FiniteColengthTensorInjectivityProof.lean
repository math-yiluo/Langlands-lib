import Langlands.Algebra.FiniteColengthTensorInjectivityStatement
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Noetherian.Defs

/-! # Proof of tensor injectivity for ideals containing maximal-ideal powers -/

universe u v

namespace Langlands.Algebra

namespace FiniteColengthTensorInjectivity

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- Tensoring the inclusion of the unit ideal is injective. -/
theorem lTensor_top_subtype_injective :
    Function.Injective (LinearMap.lTensor M (⊤ : Ideal R).subtype) := by
  refine Function.LeftInverse.injective
    (g := LinearMap.lTensor M (Submodule.topEquiv : (⊤ : Ideal R) ≃ₗ[R] R).symm.toLinearMap) ?_
  intro y
  rw [← LinearMap.lTensor_comp_apply]
  have : (Submodule.topEquiv : (⊤ : Ideal R) ≃ₗ[R] R).symm.toLinearMap ∘ₗ
      (⊤ : Ideal R).subtype = LinearMap.id := by
    ext; rfl
  rw [this, LinearMap.lTensor_id, LinearMap.id_apply]

variable [IsLocalRing R]

/-- One-step extension. If `x ∉ J` and `𝔪 x ⊆ J`, then the inclusion `J ⊆ J + R x`
stays injective after tensoring with `M`, provided `M ⊗ 𝔪 → M ⊗ R` is injective.
The proof tensors the right-exact sequence `𝔪 → J × R → J + R x`,
`a ↦ (a x, -a)`, `(j, r) ↦ j + r x`. -/
theorem lTensor_inclusion_sup_span_injective
    (hm : Function.Injective (LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype))
    (J : Ideal R) (x : R) (hxJ : x ∉ J)
    (hmx : ∀ a ∈ IsLocalRing.maximalIdeal R, a * x ∈ J) :
    Function.Injective (LinearMap.lTensor M
      (Submodule.inclusion (le_sup_left : J ≤ J ⊔ Ideal.span {x}))) := by
  set m := IsLocalRing.maximalIdeal R
  set J' := J ⊔ Ideal.span {x}
  have hxJ' : x ∈ J' := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  let f₁ : m →ₗ[R] J :=
    LinearMap.codRestrict J ((LinearMap.toSpanSingleton R R x).comp m.subtype)
      (fun a => by simpa [smul_eq_mul] using hmx a a.2)
  let f : m →ₗ[R] J × R := f₁.prod (-m.subtype)
  let g₂ : R →ₗ[R] J' :=
    LinearMap.codRestrict J' (LinearMap.toSpanSingleton R R x)
      (fun r => by simpa [smul_eq_mul] using J'.mul_mem_left r hxJ')
  let g : J × R →ₗ[R] J' := (Submodule.inclusion le_sup_left).coprod g₂
  have hexact : Function.Exact f g := by
    rintro ⟨j, r⟩
    constructor
    · intro h
      have h' : (j : R) + r * x = 0 := by
        have := congrArg Subtype.val h
        simpa [g, g₂, smul_eq_mul] using this
      have hrx : r * x = -(j : R) := eq_neg_of_add_eq_zero_right h'
      have hr : r ∈ m := by
        by_contra hr
        obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.mp hr
        apply hxJ
        have hux : (u : R) * x ∈ J := by
          rw [hrx]
          exact J.neg_mem j.2
        simpa using J.mul_mem_left (↑u⁻¹ : R) hux
      refine ⟨⟨-r, m.neg_mem hr⟩, Prod.ext (Subtype.ext ?_) ?_⟩
      · show (-r) • x = (j : R)
        rw [smul_eq_mul, neg_mul, hrx, neg_neg]
      · simp [f]
    · rintro ⟨a, ha⟩
      rw [← ha]
      apply Subtype.ext
      simp [f, f₁, g, g₂, smul_eq_mul]
  have hsurj : Function.Surjective g := by
    rintro ⟨w, hw⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact ⟨(⟨y, hy⟩, a), by apply Subtype.ext; simp [g, g₂, smul_eq_mul]⟩
  have hTexact := lTensor_exact M hexact hsurj
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hgy : LinearMap.lTensor M g (LinearMap.lTensor M (LinearMap.inl R J R) y) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, LinearMap.coprod_inl]
    exact hy
  obtain ⟨z, hz⟩ := (hTexact _).mp hgy
  have hz0 : z = 0 := by
    apply hm
    have := congrArg (LinearMap.lTensor M (LinearMap.snd R J R)) hz
    rw [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, LinearMap.snd_prod,
      LinearMap.snd_comp_inl, LinearMap.lTensor_neg, LinearMap.lTensor_zero] at this
    simpa using this
  have := congrArg (LinearMap.lTensor M (LinearMap.fst R J R)) hz
  rw [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, LinearMap.fst_comp_inl,
    LinearMap.lTensor_id, hz0, map_zero] at this
  simpa using this.symm

/-- A proper ideal containing a power of the maximal ideal admits an element outside it
that the maximal ideal multiplies into it. -/
theorem exists_not_mem_mul_mem_of_pow_le {J : Ideal R} {n : ℕ}
    (hn : IsLocalRing.maximalIdeal R ^ n ≤ J) (hJ : J ≠ ⊤) :
    ∃ x ∉ J, ∀ a ∈ IsLocalRing.maximalIdeal R, a * x ∈ J := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, top_le_iff] at hn
    exact absurd hn hJ
  | succ k ih =>
    by_cases hk : IsLocalRing.maximalIdeal R ^ k ≤ J
    · exact ih hk
    · obtain ⟨x, hxk, hxJ⟩ := SetLike.not_le_iff_exists.mp hk
      refine ⟨x, hxJ, fun a ha => hn ?_⟩
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha hxk

end FiniteColengthTensorInjectivity

open FiniteColengthTensorInjectivity in
/-- Proof of `Langlands.Algebra.FiniteColengthTensorInjectivityStatement`. -/
theorem finiteColengthTensorInjectivity :
    FiniteColengthTensorInjectivityStatement.{u, v} := by
  intro R M _ _ _ _ _ hm J n hJ
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    by_cases hJt : J = ⊤
    · subst hJt
      exact lTensor_top_subtype_injective
    · obtain ⟨x, hxJ, hmx⟩ := exists_not_mem_mul_mem_of_pow_le hJ hJt
      have hlt : J < J ⊔ Ideal.span {x} :=
        SetLike.lt_iff_le_and_exists.mpr
          ⟨le_sup_left, x, Ideal.mem_sup_right (Ideal.mem_span_singleton_self x), hxJ⟩
      have h₁ := ih _ hlt (hJ.trans le_sup_left)
      have h₂ := lTensor_inclusion_sup_span_injective hm J x hxJ hmx
      have hcomp : J.subtype =
          (J ⊔ Ideal.span {x}).subtype ∘ₗ Submodule.inclusion le_sup_left := rfl
      rw [hcomp, LinearMap.lTensor_comp, LinearMap.coe_comp]
      exact h₁.comp h₂

end Langlands.Algebra
