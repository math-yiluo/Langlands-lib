import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Coordinates for an index-two pair of fixed fields -/

noncomputable section

universe u v

namespace Langlands.FieldTheory.QuadraticFixedField

set_option autoImplicit false

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {H H' : Subgroup (K ≃ₐ[k] K)} (hHH' : H ≤ H') (hindex : H.relIndex H' = 2)
    {σ : K ≃ₐ[k] K} (hσ : σ ∈ H')

include hHH' hindex hσ in
/-- An automorphism in the larger subgroup preserves the smaller subgroup's fixed field. -/
theorem apply_mem {x : K} (hx : x ∈ IntermediateField.fixedField H) :
    σ x ∈ IntermediateField.fixedField H := by
  let τ : H' := ⟨σ, hσ⟩
  have hn : (H.subgroupOf H').Normal := Subgroup.normal_of_index_eq_two hindex
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro g hg
  let γ : H' := ⟨g, hHH' hg⟩
  have hc : σ⁻¹ * g * σ ∈ H := hn.conj_mem' γ hg τ
  have hf := hx _ hc
  change σ⁻¹ (g (σ x)) = x at hf
  simpa using congrArg σ hf

include hindex hσ in
/-- The nontrivial coset acts as an involution on the smaller subgroup's fixed field. -/
theorem apply_apply {x : K} (hx : x ∈ IntermediateField.fixedField H) :
    σ (σ x) = x := by
  have hs : σ * σ ∈ H :=
    Subgroup.mul_self_mem_of_index_two (H := H.subgroupOf H') hindex ⟨σ, hσ⟩
  exact (IntermediateField.mem_fixedField_iff _ _).mp hx (σ * σ) hs

/-- Restriction of the indicated ambient automorphism to the larger fixed field. -/
def conjugation : IntermediateField.fixedField H ≃ₐ[k] IntermediateField.fixedField H where
  toFun x := ⟨σ x, apply_mem hHH' hindex hσ x.property⟩
  invFun x := ⟨σ x, apply_mem hHH' hindex hσ x.property⟩
  left_inv x := Subtype.ext (apply_apply hindex hσ x.property)
  right_inv x := Subtype.ext (apply_apply hindex hσ x.property)
  map_mul' x y := Subtype.ext (map_mul σ (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add σ (x : K) (y : K))
  commutes' x := Subtype.ext (σ.commutes x)

@[simp] theorem conjugation_apply (x : IntermediateField.fixedField H) :
    (conjugation hHH' hindex hσ x : K) = σ x := rfl

variable (hσnot : σ ∉ H)

include hHH' hindex hσ hσnot in
/-- The lower fixed field is cut out by one additional fixedness equation. -/
theorem mem_lower_iff (x : K) :
    x ∈ IntermediateField.fixedField H' ↔
      x ∈ IntermediateField.fixedField H ∧ σ x = x := by
  constructor
  · intro hx
    exact ⟨IntermediateField.fixedField_le hHH' hx,
      (IntermediateField.mem_fixedField_iff _ _).mp hx σ hσ⟩
  · rintro ⟨hx, hs⟩
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro g hg
    by_cases hgH : g ∈ H
    · exact hx g hgH
    · have hgs : g * σ ∈ H := by
        exact (Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf H') hindex).mpr
          (show (⟨g, hg⟩ : H') ∈ H.subgroupOf H' ↔
            (⟨σ, hσ⟩ : H') ∈ H.subgroupOf H' from iff_of_false hgH hσnot)
      have hf := hx (g * σ) hgs
      change g (σ x) = x at hf
      rwa [hs] at hf

include hσnot in
/-- A trace of the quadratic involution is nonzero somewhere, also in characteristic two. -/
theorem exists_add_conjugate_ne_zero [FiniteDimensional k K] :
    ∃ e ∈ IntermediateField.fixedField H, e + σ e ≠ 0 := by
  by_contra! hall
  have hneg : -(1 : K) = 1 := by
    have h1 := hall 1 (IntermediateField.fixedField H).one_mem
    simpa using (eq_neg_of_add_eq_zero_left h1).symm
  have hfix : σ ∈ (IntermediateField.fixedField H).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : σ x = -x := eq_neg_of_add_eq_zero_right (hall x hx)
    have hminus : -x = x := by
      calc
        -x = (-1 : K) * x := by ring
        _ = x := by rw [hneg, one_mul]
    exact hx'.trans hminus
  rw [IntermediateField.fixingSubgroup_fixedField] at hfix
  exact hσnot hfix

include hHH' hindex hσ hσnot in
/-- Every anti-invariant element is a difference of an element and its conjugate. -/
theorem exists_sub_conjugate_eq [FiniteDimensional k K] {r : K} (hr : r ∈ IntermediateField.fixedField H)
    (hrσ : σ r = -r) :
    ∃ w ∈ IntermediateField.fixedField H, w - σ w = r := by
  obtain ⟨e, he, htrace⟩ := exists_add_conjugate_ne_zero (H := H) hσnot
  refine ⟨r * σ e / (e + σ e), ?_, ?_⟩
  · exact (IntermediateField.fixedField H).div_mem
      ((IntermediateField.fixedField H).mul_mem hr (apply_mem hHH' hindex hσ he))
      ((IntermediateField.fixedField H).add_mem he (apply_mem hHH' hindex hσ he))
  · rw [map_div₀, map_mul, map_add, hrσ, apply_apply hindex hσ he]
    rw [add_comm (σ e) e]
    field_simp
    ring

include hHH' hindex hσ hσnot in
/-- A nonfixed element gives affine coordinates over the lower fixed field. -/
theorem exists_linear_combination {w x : K}
    (hw : w ∈ IntermediateField.fixedField H) (hwnot : w ∉ IntermediateField.fixedField H')
    (hx : x ∈ IntermediateField.fixedField H) :
    ∃ a ∈ IntermediateField.fixedField H', ∃ b ∈ IntermediateField.fixedField H',
      x = a * w + b := by
  have hsw : σ w ≠ w := fun h => hwnot ((mem_lower_iff hHH' hindex hσ hσnot w).mpr ⟨hw, h⟩)
  have hd : w - σ w ≠ 0 := sub_ne_zero.mpr hsw.symm
  let a := (x - σ x) / (w - σ w)
  let b := x - a * w
  have haE : a ∈ IntermediateField.fixedField H :=
    (IntermediateField.fixedField H).div_mem
      ((IntermediateField.fixedField H).sub_mem hx (apply_mem hHH' hindex hσ hx))
      ((IntermediateField.fixedField H).sub_mem hw (apply_mem hHH' hindex hσ hw))
  have has : σ a = a := by
    dsimp only [a]
    rw [map_div₀, map_sub, map_sub, apply_apply hindex hσ hx, apply_apply hindex hσ hw]
    rw [← neg_sub x (σ x), ← neg_sub w (σ w), neg_div_neg_eq]
  have ha : a ∈ IntermediateField.fixedField H' :=
    (mem_lower_iff hHH' hindex hσ hσnot a).mpr ⟨haE, has⟩
  have hbE : b ∈ IntermediateField.fixedField H :=
    (IntermediateField.fixedField H).sub_mem hx ((IntermediateField.fixedField H).mul_mem haE hw)
  have hbs : σ b = b := by
    dsimp only [b]
    rw [map_sub, map_mul, has]
    dsimp only [a]
    field_simp
    ring
  refine ⟨a, ha, b, (mem_lower_iff hHH' hindex hσ hσnot b).mpr ⟨hbE, hbs⟩, ?_⟩
  dsimp only [b]
  ring

include hHH' hindex hσ hσnot in
/-- Each nonzero element is a lower-field multiple of one or of a translate of `w`. -/
theorem unit_decomposition {w : K}
    (hw : w ∈ IntermediateField.fixedField H) (hwnot : w ∉ IntermediateField.fixedField H')
    (x : Kˣ) (hx : (x : K) ∈ IntermediateField.fixedField H) :
    ∃ a : Kˣ, (a : K) ∈ IntermediateField.fixedField H' ∧
      ((x : K) = (a : K) ∨ ∃ b ∈ IntermediateField.fixedField H',
        (x : K) = (a : K) * (w + b)) := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_linear_combination hHH' hindex hσ hσnot hw hwnot hx
  by_cases ha0 : a = 0
  · have hxb : (x : K) = b := by simpa [ha0] using hab
    exact ⟨x, hxb ▸ hb, Or.inl rfl⟩
  · refine ⟨Units.mk0 a ha0, ha, Or.inr ⟨b / a, (IntermediateField.fixedField H').div_mem hb ha, ?_⟩⟩
    change (x : K) = a * (w + b / a)
    rw [hab]
    field_simp

end Langlands.FieldTheory.QuadraticFixedField
