import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main
import Mathlib.FieldTheory.Galois.Basic

/-!
# The norm group of a quadratic extension of local fields

For a quadratic Galois extension `E / F` of nonarchimedean local fields, the norms
`N_{E/F}(Eˣ)` form a subgroup of index two of `Fˣ`
(`index_range_norm_eq_two`); equivalently the product of two non-norms is a norm
(`mul_mem_range_norm_of_finrank_eq_two`). Both are read off from local reciprocity, in the form
of the separate library NYLL: the local norm-residue symbol
`LocalClassFieldTheory.localArtinMonoidHom F E : Fˣ →* Gal(E/F)ᵃᵇ` is surjective with kernel the
norm group, and `Gal(E/F)` has order two.

`normResidueSign F E : Fˣ →* ℤˣ` is the quadratic character of `F` attached to `E`: `1` on norms,
`-1` elsewhere (`normResidueSign_eq_one_iff`).
-/

namespace Langlands.LocalClassField

open LocalFieldTheory LocalClassFieldTheory

/-- In a group of order at most two, the product of two non-trivial elements is trivial. -/
private theorem mul_eq_one_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2)
    {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) : a * b = 1 := by
  have : Nontrivial G := nontrivial_of_ne a 1 ha
  have h2 : Nat.card G = 2 := le_antisymm h Finite.one_lt_card
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : G)).1 h2
  have hab : b = a := (hy b hb).trans (hy a ha).symm
  rw [hab, ← pow_two, ← h2, pow_card_eq_one']

/-- The image of the norm on units is NYLL's norm subgroup. -/
theorem range_unitsMap_norm_eq_localNormSubgroup (F E : Type) [Field F] [Field E]
    [Algebra F E] : (Units.map (Algebra.norm F : E →* F)).range = localNormSubgroup F E := by
  ext x
  simp only [MonoidHom.mem_range, localNormSubgroup]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, Units.ext (normUnits_apply_coe F E w)⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, Units.ext (normUnits_apply_coe F E w).symm⟩

section

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field E] [Algebra F E] [IsGalois F E]

/-- **The product of two non-norms is a norm** in a quadratic Galois extension of
nonarchimedean local fields. -/
theorem mul_mem_range_norm_of_finrank_eq_two (h : Module.finrank F E = 2) {x y : Fˣ}
    (hx : x ∉ (Units.map (Algebra.norm F : E →* F)).range)
    (hy : y ∉ (Units.map (Algebra.norm F : E →* F)).range) :
    x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h
  rw [range_unitsMap_norm_eq_localNormSubgroup, ← localArtinMonoidHom_ker] at hx hy ⊢
  rw [MonoidHom.mem_ker] at hx hy ⊢
  have hG : Nat.card Gal(E/F) = 2 := by rw [IsGalois.card_aut_eq_finrank, h]
  have : Finite Gal(E/F) := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have hA : Nat.card (Abelianization Gal(E/F)) ≤ 2 :=
    hG ▸ Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have : Finite (Abelianization Gal(E/F)) := Finite.of_surjective _ QuotientGroup.mk_surjective
  rw [map_mul]
  exact mul_eq_one_of_card_le_two hA hx hy

/-- **The norm group of a quadratic Galois extension of nonarchimedean local fields has index
two.** -/
theorem index_range_norm_eq_two (h : Module.finrank F E = 2) :
    (Units.map (Algebra.norm F : E →* F)).range.index = 2 := by
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h
  have : Algebra.IsQuadraticExtension F E := ⟨h⟩
  have hG : Nat.card Gal(E/F) = 2 := by rw [IsGalois.card_aut_eq_finrank, h]
  have : Finite Gal(E/F) := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  rw [range_unitsMap_norm_eq_localNormSubgroup, ← localArtinMonoidHom_ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (localArtinMonoidHom_surjective F E), Subgroup.card_top]
  -- `Gal(E/F)` is commutative, so it injects into its abelianization.
  have hinj : Function.Injective (Abelianization.of : Gal(E/F) →* _) := by
    intro a b hab
    simpa using congrArg (Abelianization.lift (MonoidHom.id Gal(E/F))) hab
  have : Finite (Abelianization Gal(E/F)) := Finite.of_surjective _ QuotientGroup.mk_surjective
  exact le_antisymm (hG ▸ Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective)
    (hG ▸ Nat.card_le_card_of_injective _ hinj)

end

open Classical in
/-- The quadratic character of `F` attached to a quadratic Galois extension `E` of
nonarchimedean local fields: `1` on the norms from `Eˣ`, `-1` elsewhere. It is a homomorphism
because the norms have index two (`mul_mem_range_norm_of_finrank_eq_two`). -/
noncomputable def normResidueSign (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [IsGalois F E] : Fˣ →* ℤˣ where
  toFun t := if t ∈ (Units.map (Algebra.norm F : E →* F)).range then 1 else -1
  map_one' := ite_eq_left (one_mem _)
  map_mul' s t := by
    set H := (Units.map (Algebra.norm F : E →* F)).range
    by_cases hs : s ∈ H <;> by_cases ht : t ∈ H
    · simp [hs, ht, H.mul_mem hs ht]
    · have : s * t ∉ H := fun h => ht ((H.mul_mem_cancel_left hs).mp h)
      simp [hs, ht, this]
    · have : s * t ∉ H := fun h => hs ((H.mul_mem_cancel_right ht).mp h)
      simp [hs, ht, this]
    · have : s * t ∈ H := mul_mem_range_norm_of_finrank_eq_two
        (Algebra.IsQuadraticExtension.finrank_eq_two F E) hs ht
      simp [hs, ht, this]

section

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [IsGalois F E]

theorem normResidueSign_of_mem {a : Fˣ} (h : a ∈ (Units.map (Algebra.norm F : E →* F)).range) :
    normResidueSign F E a = 1 := by
  classical
  simp only [normResidueSign, MonoidHom.coe_mk, OneHom.coe_mk]
  convert ite_eq_left h

theorem normResidueSign_of_notMem {a : Fˣ}
    (h : a ∉ (Units.map (Algebra.norm F : E →* F)).range) : normResidueSign F E a = -1 := by
  classical
  simp only [normResidueSign, MonoidHom.coe_mk, OneHom.coe_mk]
  convert ite_eq_right h

theorem normResidueSign_eq_one_iff {a : Fˣ} :
    normResidueSign F E a = 1 ↔ a ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  refine ⟨fun h => ?_, normResidueSign_of_mem⟩
  by_contra h'
  rw [normResidueSign_of_notMem h'] at h
  exact absurd h (by decide)

theorem normResidueSign_eq_neg_one_iff {a : Fˣ} :
    normResidueSign F E a = -1 ↔ a ∉ (Units.map (Algebra.norm F : E →* F)).range := by
  refine ⟨fun h h' => ?_, normResidueSign_of_notMem⟩
  rw [normResidueSign_of_mem h'] at h
  exact absurd h (by decide)

@[simp]
theorem normResidueSign_norm (z : Eˣ) :
    normResidueSign F E (Units.map (Algebra.norm F : E →* F) z) = 1 :=
  normResidueSign_of_mem ⟨z, rfl⟩

/-- The `n`-th power of the quadratic character, as a complex number. -/
theorem normResidueSign_pow_eq_ite (a : Fˣ) (n : ℕ)
    [Decidable (a ∈ (Units.map (Algebra.norm F : E →* F)).range)] :
    ((normResidueSign F E a : ℤ) : ℂ) ^ n =
      if a ∈ (Units.map (Algebra.norm F : E →* F)).range then 1 else (-1) ^ n := by
  split_ifs with h
  · simp [normResidueSign_of_mem h]
  · simp [normResidueSign_of_notMem h]

end

end Langlands.LocalClassField
