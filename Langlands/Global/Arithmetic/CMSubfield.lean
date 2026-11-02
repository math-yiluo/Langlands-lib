import Mathlib.NumberTheory.NumberField.CMField
import Langlands.Global.Arithmetic.QuadraticRootSupport

/-!
# Subfields of Galois CM fields containing an imaginary square root

Complex conjugation of a Galois CM field is central in the Galois group, so it preserves
every intermediate field. A field mapping into such a CM field, stable under complex
conjugation and containing a square root of a negative rational number, is again a CM
field. Every element is `y₁ + y₂ x` with `y₁, y₂` totally real and `x` the square root.
-/

namespace Langlands.Global.CMRealization

open NumberField IntermediateField ComplexEmbedding

section Central

variable {M : Type*} [Field M] [NumberField M] [IsGalois ℚ M]

/-- An intermediate field of a Galois number field is stable under a central
automorphism. -/
theorem mem_of_central (S : IntermediateField ℚ M) {u : M ≃ₐ[ℚ] M}
    (hu : ∀ (σ : M ≃ₐ[ℚ] M) (x : M), σ (u x) = u (σ x)) {x : M} (hx : x ∈ S) :
    u x ∈ S := by
  rw [← IsGalois.fixedField_fixingSubgroup S, mem_fixedField_iff]
  intro σ hσ
  rw [hu, (mem_fixingSubgroup_iff _ _).mp hσ x hx]

end Central

section NegativeSquare

variable {K : Type*} [Field K] [CharZero K] {a : ℚ} {x : K}

theorem complex_sq_ne_of_isReal (ha : a < 0) {z : ℂ} (hz : (starRingEnd ℂ) z = z) :
    z ^ 2 ≠ (a : ℂ) := by
  intro h
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hz
  have hre := congrArg Complex.re h
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.ratCast_re] at hre
  have ha' : (a : ℝ) < 0 := by exact_mod_cast ha
  nlinarith [mul_self_nonneg z.re]

/-- A field containing a square root of a negative rational number is totally complex. -/
theorem isTotallyComplex_of_sq_neg (ha : a < 0) (hx : x ^ 2 = algebraMap ℚ K a) :
    IsTotallyComplex K := by
  refine ⟨fun w => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hw
  apply complex_sq_ne_of_isReal ha (z := w.embedding x)
  · exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hw) x
  · rw [← map_pow, hx, eq_ratCast, map_ratCast]

/-- A square root of a negative rational number is not totally real. -/
theorem not_mem_maximalRealSubfield_of_sq_neg [Nonempty (K →+* ℂ)] (ha : a < 0)
    (hx : x ^ 2 = algebraMap ℚ K a) : x ∉ maximalRealSubfield K := by
  intro h
  let φ : K →+* ℂ := Classical.choice inferInstance
  apply complex_sq_ne_of_isReal ha (z := φ x) (h φ)
  rw [← map_pow, hx, eq_ratCast, map_ratCast]

/-- A field generated over its maximal real subfield by a square root of a negative
rational number is a CM field. -/
theorem isCMField_of_adjoin_eq_top [Nonempty (K →+* ℂ)] (ha : a < 0)
    (hx : x ^ 2 = algebraMap ℚ K a) (htop : (maximalRealSubfield K)⟮x⟯ = ⊤) : IsCMField K := by
  have hxr := not_mem_maximalRealSubfield_of_sq_neg ha hx
  have := isTotallyComplex_of_sq_neg ha hx
  set R := maximalRealSubfield K
  have hxR : x ^ 2 = algebraMap R K (algebraMap ℚ R a) := by
    rw [hx, ← IsScalarTower.algebraMap_apply]
  have hns : ¬ IsSquare (algebraMap ℚ R a) := by
    rintro ⟨b, hb⟩
    have hb' : ((b : K)) ^ 2 = x ^ 2 := by
      rw [hxR, hb, pow_two, map_mul]
      rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb' with h | h
    · exact hxr (h ▸ b.2)
    · exact hxr (by rw [← neg_neg x, ← h]; exact R.neg_mem b.2)
  have h2 : Module.finrank R K = 2 := by
    rw [← IntermediateField.finrank_top', ← htop]
    exact Langlands.Global.squareRoot_finrank hns hxR
  exact { is_quadratic := { finrank_eq_two' := h2 } }

end NegativeSquare

section Conj

variable (M : Type*) [Field M] [NumberField M] [IsCMField M]

/-- Complex conjugation of a CM field, as a rational algebra automorphism. -/
noncomputable def conjQ : M ≃ₐ[ℚ] M :=
  AlgEquiv.ofRingEquiv (f := (IsCMField.complexConj M).toRingEquiv) fun r => by
    simp only [eq_ratCast, map_ratCast]

variable {M}

theorem conjQ_apply (x : M) : conjQ M x = IsCMField.complexConj M x := rfl

theorem conjQ_conjQ (x : M) : conjQ M (conjQ M x) = x :=
  IsCMField.complexConj_apply_apply M x

theorem embedding_conjQ (φ : M →+* ℂ) (x : M) : φ (conjQ M x) = starRingEnd ℂ (φ x) :=
  IsCMField.complexEmbedding_complexConj M φ x

theorem conjQ_eq_self_iff (x : M) : conjQ M x = x ↔ x ∈ maximalRealSubfield M :=
  IsCMField.complexConj_eq_self_iff M x

/-- Complex conjugation commutes with every automorphism of a CM field. -/
theorem conjQ_central (σ : M ≃ₐ[ℚ] M) (x : M) : σ (conjQ M x) = conjQ M (σ x) := by
  let φ : M →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := embedding_conjQ (φ.comp (σ : M →+* M)) x
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at h
  rw [h, embedding_conjQ]

/-- A square root of a negative rational number is negated by complex conjugation. -/
theorem conjQ_of_sq_neg {a : ℚ} (ha : a < 0) {x : M} (hx : x ^ 2 = algebraMap ℚ M a) :
    conjQ M x = -x := by
  have hc : (conjQ M x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, AlgEquiv.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with h | h
  · exact absurd ((conjQ_eq_self_iff x).mp h) (not_mem_maximalRealSubfield_of_sq_neg ha hx)
  · exact h

end Conj

section Subfield

variable {M : Type*} [Field M] [NumberField M] [IsCMField M]
  {S : Type*} [Field S] [CharZero S] [Algebra S M]

/-- An element of `S` whose image is fixed by complex conjugation is totally real. -/
theorem mem_maximalRealSubfield_of_conjQ {y : S}
    (hy : conjQ M (algebraMap S M y) = algebraMap S M y) : y ∈ maximalRealSubfield S := by
  have : Algebra.IsAlgebraic S M := by
    have : Module.Finite S M := Module.Finite.of_restrictScalars_finite ℚ S M
    infer_instance
  intro ψ
  have h := embedding_conjQ (ComplexEmbedding.lift M ψ) (algebraMap S M y)
  rw [hy, ComplexEmbedding.lift_algebraMap_apply] at h
  exact h.symm

variable (hS : ∀ y : S, ∃ z : S, algebraMap S M z = conjQ M (algebraMap S M y))
  {a : ℚ} (ha : a < 0) {x : S} (hx : x ^ 2 = algebraMap ℚ S a)

include hS ha hx in
/-- Every element is `y₁ + y₂ x` with totally real `y₁, y₂`. -/
theorem exists_real_decomposition (y : S) :
    ∃ y₁ ∈ maximalRealSubfield S, ∃ y₂ ∈ maximalRealSubfield S, y = y₁ + y₂ * x := by
  have hxM : (algebraMap S M x) ^ 2 = algebraMap ℚ M a := by
    rw [← map_pow, hx, ← IsScalarTower.algebraMap_apply]
  have hcx := conjQ_of_sq_neg ha hxM
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (algebraMap ℚ S a) = 0 := by rw [← hx]; ring
    simp only [map_eq_zero] at this
    exact ha.ne this
  obtain ⟨z, hz⟩ := hS y
  refine ⟨(y + z) / 2, mem_maximalRealSubfield_of_conjQ (M := M) ?_, (y - z) / (2 * x),
    mem_maximalRealSubfield_of_conjQ (M := M) ?_, ?_⟩
  · simp only [map_div₀, map_add, map_ofNat, hz, conjQ_conjQ]
    ring
  · have hxM0 : algebraMap S M x ≠ 0 := (map_ne_zero _).mpr hx0
    simp only [map_div₀, map_sub, map_mul, map_ofNat, hz, conjQ_conjQ, hcx]
    field_simp
    ring
  · field_simp
    ring

include hS ha hx in
theorem isCMField_of_sq_neg : IsCMField S := by
  have hreal := exists_real_decomposition hS ha hx
  have : Nonempty (S →+* ℂ) :=
    ⟨(Classical.choice (inferInstance : Nonempty (M →+* ℂ))).comp (algebraMap S M)⟩
  refine isCMField_of_adjoin_eq_top ha hx ?_
  rw [eq_top_iff]
  intro y _
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hreal y
  have hgen : x ∈ (maximalRealSubfield S)⟮x⟯ := mem_adjoin_simple_self _ x
  have h₁ : y₁ ∈ (maximalRealSubfield S)⟮x⟯ :=
    IntermediateField.algebraMap_mem _ (⟨y₁, hy₁⟩ : maximalRealSubfield S)
  have h₂ : y₂ ∈ (maximalRealSubfield S)⟮x⟯ :=
    IntermediateField.algebraMap_mem _ (⟨y₂, hy₂⟩ : maximalRealSubfield S)
  exact add_mem h₁ (mul_mem h₂ hgen)

include hS ha hx in
/-- The maximal real subfield and any subfield containing the square root generate. -/
theorem maximalRealSubfield_sup_eq_top (T : Subfield S) (hxT : x ∈ T) :
    maximalRealSubfield S ⊔ T = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := exists_real_decomposition hS ha hx y
  exact add_mem (le_sup_left (a := maximalRealSubfield S) (b := T) hy₁)
    (mul_mem (le_sup_left (a := maximalRealSubfield S) (b := T) hy₂)
      (le_sup_right (a := maximalRealSubfield S) (b := T) hxT))

/-- Complex conjugation of a CM field `S` mapping into `M` is the restriction of the
complex conjugation of `M`. -/
theorem algebraMap_complexConj [NumberField S] [IsCMField S] (y : S) :
    algebraMap S M (IsCMField.complexConj S y) = conjQ M (algebraMap S M y) := by
  let φ : M →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := IsCMField.complexEmbedding_complexConj S (φ.comp (algebraMap S M)) y
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  rw [h, embedding_conjQ]

end Subfield

end Langlands.Global.CMRealization
