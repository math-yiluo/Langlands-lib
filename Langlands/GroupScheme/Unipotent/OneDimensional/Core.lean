import Langlands.GroupScheme.Unipotent.OneDimensional.Relation
import Langlands.GroupScheme.Unipotent.PrimitiveCoordinate
import Langlands.GroupScheme.Unipotent.AdditiveQuotient

/-! # A primitive coordinate generating the coordinate ring -/

noncomputable section

universe u

open CategoryTheory Polynomial TensorProduct
open Algebra.TensorProduct (includeLeft includeRight)

namespace Langlands.GroupScheme.Unipotent.OneDimensional

open AffineLinearEmbedding Chevalley

section Primitive

variable {k B : Type*} [Field k] [CommRing B] [Bialgebra k B]

/-- An additive polynomial in a primitive element is primitive. -/
theorem IsAdditive.isPrimitiveElem_aeval {f : k[X]} (hf : IsAdditive f) {u : B}
    (hu : Bialgebra.IsPrimitiveElem k u) : Bialgebra.IsPrimitiveElem k (aeval u f) := by
  rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
  have h := aeval_algHom_apply (Bialgebra.comulAlgHom k B) u f
  simp only [Bialgebra.comulAlgHom_apply, hu.comul_eq_tmul_add_tmul] at h
  have hL : aeval (u ⊗ₜ[k] (1 : B)) f = aeval u f ⊗ₜ[k] (1 : B) :=
    aeval_algHom_apply (includeLeft : B →ₐ[k] B ⊗[k] B) u f
  have hR : aeval ((1 : B) ⊗ₜ[k] u) f = (1 : B) ⊗ₜ[k] aeval u f :=
    aeval_algHom_apply (includeRight : B →ₐ[k] B ⊗[k] B) u f
  rw [← h, hf.aeval_add, hL, hR]

/-- A nonzero primitive element of a domain is transcendental. -/
theorem transcendental_of_isPrimitiveElem [IsDomain B] {u : B}
    (hu : Bialgebra.IsPrimitiveElem k u) (hu0 : u ≠ 0) : Transcendental k u :=
  transcendental_of_augmentation_eq_zero (Bialgebra.counitAlgHom k B) hu0
    (by simpa using hu.counit_eq_zero)

/-- **Euclid's algorithm for primitive elements.** Over a perfect field, two primitive
elements of a domain satisfying a nontrivial additive relation are additive polynomials in a
single primitive element. -/
theorem exists_common_of_primitive [PerfectField k] [IsDomain B] {y t : B}
    (hy : Bialgebra.IsPrimitiveElem k y) (ht : Bialgebra.IsPrimitiveElem k t) {α β : k[X]}
    (hα : IsAdditive α) (hβ : IsAdditive β) (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    (hrel : aeval y α = aeval t β) :
    ∃ s : B, Bialgebra.IsPrimitiveElem k s ∧ ∃ A A' : k[X], IsAdditive A ∧ IsAdditive A' ∧
      y = aeval s A ∧ t = aeval s A' := by
  obtain ⟨q, hq⟩ := ExpChar.exists k
  obtain ⟨s, hs, A, A', hA, hA', hys, hts⟩ :=
    exists_common_of_relation q {u : B | Bialgebra.IsPrimitiveElem k u}
      (fun u hu A hA => hA.isPrimitiveElem_aeval hu) (fun u hu v hv => hu.sub hv)
      (fun u hu A hA0 hAu => by
        by_contra hu0
        exact transcendental_of_isPrimitiveElem hu hu0 ⟨A, hA0, hAu⟩)
      _ y t α β le_rfl hy ht hα hβ hα0 hβ0 hrel
  exact ⟨s, hs, A, A', hA, hA', hys, hts⟩

end Primitive

section Finrank

variable {k B : Type*} [Field k] [CommRing B] [IsDomain B] [Algebra k B]

/-- Dividing by a proper factor lowers the dimension of the quotient. -/
theorem finrank_quotient_span_lt {s b : B} (hs : s ≠ 0) (hb : ¬ IsUnit b)
    [Module.Finite k (B ⧸ Ideal.span {s * b})] :
    Module.finrank k (B ⧸ Ideal.span {s}) < Module.finrank k (B ⧸ Ideal.span {s * b}) := by
  have hle : Ideal.span {s * b} ≤ Ideal.span {s} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right s b)
  let g := (Ideal.Quotient.factorₐ k hle).toLinearMap
  have hsurj : Function.Surjective g := Ideal.Quotient.factor_surjective hle
  have hker : LinearMap.ker g ≠ ⊥ := by
    intro h
    have hmem : Ideal.Quotient.mk (Ideal.span {s * b}) s ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker]
      change Ideal.Quotient.mk (Ideal.span {s}) s = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self s
    rw [h, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    apply hb
    refine IsUnit.of_mul_eq_one c (mul_left_cancel₀ hs ?_)
    rw [mul_one, ← mul_assoc, ← hc]
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h1
  have h2 : 0 < Module.finrank k (LinearMap.ker g) :=
    Nat.pos_of_ne_zero fun h => hker (Submodule.finrank_eq_zero.mp h)
  omega

end Finrank

section Core

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- **The algebraic core.** Over a perfect field, let `B` be a unipotent coordinate ring with
`B` and `B ⊗ B` domains and `B ≠ k`, such that for every nonzero primitive `z`, `B / zB` is
finite-dimensional and no nonconstant polynomial in `z` is a unit, and any two primitive
elements are algebraically dependent. Then `B = k[y]` for a primitive element `y`
transcendental over `k`. -/
theorem exists_primitive_bijective [PerfectField k] [IsDomain B] [IsDomain (B ⊗[k] B)]
    (hB : letI := bialgebra e; OneMemStable k B)
    (hconst : ∃ a : B, a ∉ k ∙ (1 : B))
    (hfin : ∀ z : B, (letI := bialgebra e; Bialgebra.IsPrimitiveElem k z) → z ≠ 0 →
      Module.Finite k (B ⧸ Ideal.span {z}))
    (hdep : ∀ y t : B, (letI := bialgebra e; Bialgebra.IsPrimitiveElem k y) →
      (letI := bialgebra e; Bialgebra.IsPrimitiveElem k t) →
      ∃ c : k[X][X], c ≠ 0 ∧ ev2 y t c = 0)
    (hunit : ∀ z : B, (letI := bialgebra e; Bialgebra.IsPrimitiveElem k z) → z ≠ 0 →
      ∀ g : k[X], 0 < g.natDegree → ¬ IsUnit (aeval z g)) :
    ∃ y : B, (letI := bialgebra e; Bialgebra.IsPrimitiveElem k y) ∧
      Function.Bijective (aeval y : k[X] →ₐ[k] B) := by
  classical
  let := bialgebra e
  have hex : ∃ n, ∃ y : B, Bialgebra.IsPrimitiveElem k y ∧ y ≠ 0 ∧
      Module.finrank k (B ⧸ Ideal.span {y}) = n := by
    obtain ⟨y, hy0, hy⟩ := exists_nonzero_primitive_of_oneMemStable hB hconst
    exact ⟨_, y, hy, hy0, rfl⟩
  obtain ⟨y, hy, hy0, hyn⟩ := Nat.find_spec hex
  have hmin : ∀ z : B, Bialgebra.IsPrimitiveElem k z → z ≠ 0 →
      Module.finrank k (B ⧸ Ideal.span {y}) ≤ Module.finrank k (B ⧸ Ideal.span {z}) :=
    fun z hz hz0 => hyn ▸ Nat.find_min' hex ⟨z, hz, hz0, rfl⟩
  refine ⟨y, hy, transcendental_iff_injective.mp (transcendental_of_isPrimitiveElem hy hy0), ?_⟩
  intro b
  by_contra hb
  have hb' : b ∉ polys (k := k) y := fun ⟨f, hf⟩ => hb ⟨f, hf⟩
  obtain ⟨t, ht, htp⟩ := exists_primitive_not_mem_polys e hB hy hy0 (hfin y hy hy0) hb'
  obtain ⟨c, hc0, hc⟩ := hdep y t hy ht
  obtain ⟨α, β, hα, hβ, hne, hrel⟩ := exists_additive_relation hy ht hc0 hc
  have htr : ∀ u : B, Bialgebra.IsPrimitiveElem k u → ∀ A : k[X], A ≠ 0 → aeval u A = 0 →
      u = 0 := fun u hu A hA0 hAu => by
    by_contra hu0
    exact transcendental_of_isPrimitiveElem hu hu0 ⟨A, hA0, hAu⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htp (Submodule.zero_mem _)
  have hα0 : α ≠ 0 := by
    rintro rfl
    have hβ0 : β ≠ 0 := hne.resolve_left (not_not.mpr rfl)
    rw [map_zero, zero_add] at hrel
    exact ht0 (htr t ht β hβ0 hrel)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [map_zero, add_zero] at hrel
    exact hy0 (htr y hy α hα0 hrel)
  obtain ⟨s, hs, A, A', hA, hA', hys, hts⟩ :=
    exists_common_of_primitive hy ht hα hβ.neg hα0 (neg_ne_zero.mpr hβ0)
      (by rw [map_neg]; exact eq_neg_of_add_eq_zero_left hrel)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hy0 (hys.trans hA.aeval_zero)
  by_cases hdeg : A.natDegree ≤ 1
  · -- `y` is a nonzero multiple of `s`, so `t ∈ k[s] = k[y]`.
    have hAeq : A = C (A.coeff 1) * X := by
      have h := eq_X_add_C_of_natDegree_le_one hdeg
      rwa [hA.coeff_zero, C_0, add_zero] at h
    set a := A.coeff 1 with ha
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, C_0, zero_mul] at hAeq
      rw [hAeq, map_zero] at hys
      exact hy0 hys
    have hsy : s = aeval y (C a⁻¹ * X) := by
      rw [hys, hAeq]
      simp only [map_mul, aeval_C, aeval_X]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_mul]
    apply htp
    rw [hts, hsy, ← aeval_comp]
    exact aeval_mem_polys y _
  · -- `y = s · A₁(s)` with `A₁(s)` not a unit, contradicting minimality.
    obtain ⟨A₁, hA₁⟩ := X_dvd_iff.mpr hA.coeff_zero
    have hA0 : A ≠ 0 := by
      rintro rfl
      exact hdeg (by simp)
    have hA₁0 : A₁ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hA₁
      exact hA0 hA₁
    have hpos : 0 < A₁.natDegree := by
      rw [hA₁, natDegree_X_mul hA₁0] at hdeg
      omega
    have hyeq : y = s * aeval s A₁ := by
      rw [hys, hA₁, map_mul, aeval_X]
    have : Module.Finite k (B ⧸ Ideal.span {s * aeval s A₁}) := hyeq ▸ hfin y hy hy0
    have hlt := finrank_quotient_span_lt (k := k) hs0 (hunit s hs hs0 A₁ hpos)
    rw [← hyeq] at hlt
    exact absurd (hmin s hs hs0) (not_le.mpr hlt)

end Core

end Langlands.GroupScheme.Unipotent.OneDimensional
