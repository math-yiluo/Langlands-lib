import Langlands.Correspondence.Laumon.CompletionConstants
import Langlands.LocalFactor.Ramification.LocalClosureLower

/-!
# Density of the henselian elements in the finite levels of `k((t))`

For a finite field `k`, the end field `endField k` is dense in `LaurentSeries k`. If restriction
`completionRestriction k` is a homeomorphism, every finite Galois extension `L` of
`LaurentSeries k` inside its separable closure is spanned over `LaurentSeries k` by its henselian
elements `L ∩ endGenericClosure k`, which are therefore dense in `L` for the Library's
`closureValuation`.
-/

noncomputable section

universe u

namespace Langlands.Henniart.Laumon

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

open IsLocalRing ValuativeRel
open Langlands.LocalGalois Langlands.LocalGalois.SepClosed
open scoped NNReal

section Approximation

theorem mul_lt_of_lt_div_add_one {a d γ : ℝ≥0} (h : d < γ / (a + 1)) : a * d < γ := by
  have ha : (0 : ℝ≥0) < a + 1 := add_pos_of_nonneg_of_pos zero_le one_pos
  have h1 : d * (a + 1) < γ := (lt_div_iff₀ ha).mp h
  calc a * d ≤ d * (a + 1) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) zero_le
    _ < γ := h1

theorem div_add_one_pos {a γ : ℝ≥0} (hγ : 0 < γ) : 0 < γ / (a + 1) :=
  div_pos hγ (add_pos_of_nonneg_of_pos zero_le one_pos)

end Approximation

section Density

variable (k : Type u) [Field k] [Finite k]

local instance : NontriviallyNormedField (LaurentSeries k) := localNormedField (LaurentSeries k)
local instance : IsUltrametricDist (LaurentSeries k) := localNormedField_ultrametric _
local instance : CompleteSpace (LaurentSeries k) := localNormedField_complete _

local notation "X" => LaurentSeries k
local notation "Ωx" => SeparableClosure (LaurentSeries k)

/-- The end field is dense in `k((t))` for the Library's valuation of the separable closure. -/
theorem exists_endField_closureValuation_lt (a : X) {γ : ℝ≥0} (hγ : 0 < γ) :
    ∃ c : endField k,
      closureValuation X Ωx (algebraMap X Ωx a - algebraMap X Ωx (c : X)) < γ := by
  obtain ⟨f, hf⟩ := Metric.denseRange_iff.mp (LaurentSeries.coe_range_dense (K := k)) a γ hγ
  refine ⟨algebraMap (RatFunc k) (endField k) f, ?_⟩
  rw [← map_sub, ← NNReal.coe_lt_coe]
  change spectralNorm X Ωx (algebraMap X Ωx (a - (f : X))) < (γ : ℝ)
  rw [spectralNorm_extends, ← dist_eq_norm]
  exact hf

variable {k}

/-- The henselian elements of a finite level `L`: the elements of `L` that lie in the separable
generic closure. -/
def henselianLevel (L : FiniteGaloisIntermediateField X Ωx) : Subfield Ωx :=
  (endGenericClosure k).toSubfield ⊓ L.toSubfield

omit [Finite k] in
theorem mem_henselianLevel {L : FiniteGaloisIntermediateField X Ωx} {y : Ωx} :
    y ∈ henselianLevel L ↔ y ∈ endGenericClosure k ∧ y ∈ L.toIntermediateField :=
  Iff.rfl

variable (hr : IsHomeomorph (completionRestriction k))
include hr

/-- **Galois correspondence across the completion.** If restriction is a homeomorphism, every
finite Galois level `L` is generated over `k((t))` by its henselian elements. -/
theorem le_adjoin_henselianLevel (L : FiniteGaloisIntermediateField X Ωx) :
    L.toIntermediateField ≤ IntermediateField.adjoin X (henselianLevel L : Set Ωx) := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup
    (IntermediateField.adjoin X (henselianLevel L : Set Ωx))]
  intro x hx
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hσS : ∀ y ∈ henselianLevel L, σ y = y := fun y hy =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ y
      (IntermediateField.subset_adjoin _ _ hy)
  let H : ClosedSubgroup Gal(endGenericClosure k/endField k) :=
    ⟨(L.toIntermediateField.fixingSubgroup).map (completionRestriction k), by
      exact hr.isClosedMap _ L.toIntermediateField.fixingSubgroup_isClosed⟩
  have hmem : completionRestriction k σ ∈
      (IntermediateField.fixedField (H : Subgroup _)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hyL : (y : Ωx) ∈ L.toIntermediateField := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L.toIntermediateField,
        IntermediateField.mem_fixedField_iff]
      intro σ' hσ'
      have h1 := (IntermediateField.mem_fixedField_iff _ _).mp hy
        (completionRestriction k σ') ⟨σ', hσ', rfl⟩
      rw [← completionRestriction_apply]
      exact congrArg Subtype.val h1
    apply Subtype.ext
    rw [completionRestriction_apply]
    exact hσS _ ⟨y.property, hyL⟩
  rw [InfiniteGalois.fixingSubgroup_fixedField H] at hmem
  obtain ⟨σ', hσ', heq⟩ := hmem
  rw [hr.bijective.injective heq] at hσ'
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ' x hx

/-- **Density of the henselian elements.** If restriction is a homeomorphism, every element of a
finite Galois level `L` is approximated arbitrarily well by henselian elements of `L`. -/
theorem exists_henselianLevel_closureValuation_lt (L : FiniteGaloisIntermediateField X Ωx)
    {x : Ωx} (hx : x ∈ L.toIntermediateField) {γ : ℝ≥0} (hγ : 0 < γ) :
    ∃ b ∈ henselianLevel L, closureValuation X Ωx (x - b) < γ := by
  let D : Submodule X Ωx :=
    { carrier := {x | ∀ γ : ℝ≥0, 0 < γ → ∃ b ∈ henselianLevel L,
        closureValuation X Ωx (x - b) < γ}
      zero_mem' := fun γ hγ => ⟨0, zero_mem _, by simpa using hγ⟩
      add_mem' := by
        intro x y hx hy γ hγ
        obtain ⟨b, hb, hxb⟩ := hx γ hγ
        obtain ⟨b', hb', hyb⟩ := hy γ hγ
        refine ⟨b + b', add_mem hb hb', ?_⟩
        rw [add_sub_add_comm]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hxb hyb)
      smul_mem' := by
        intro a x hx γ hγ
        obtain ⟨b, hb, hxb⟩ := hx _ (div_add_one_pos (a := closureValuation X Ωx
          (algebraMap X Ωx a)) hγ)
        obtain ⟨c, hc⟩ := exists_endField_closureValuation_lt k a
          (div_add_one_pos (a := closureValuation X Ωx b) hγ)
        have hcS : algebraMap X Ωx (c : X) ∈ henselianLevel L := by
          refine ⟨?_, L.toIntermediateField.algebraMap_mem _⟩
          exact (algebraMap (endField k) (endGenericClosure k) c).property
        refine ⟨algebraMap X Ωx (c : X) * b, mul_mem hcS hb, ?_⟩
        have hsplit : a • x - algebraMap X Ωx (c : X) * b =
            algebraMap X Ωx a * (x - b) + (algebraMap X Ωx a - algebraMap X Ωx (c : X)) * b := by
          rw [Algebra.smul_def]
          ring
        rw [hsplit]
        refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
        · rw [map_mul]
          exact mul_lt_of_lt_div_add_one hxb
        · rw [map_mul, mul_comm]
          exact mul_lt_of_lt_div_add_one hc }
  have hspan : ∀ y ∈ IntermediateField.adjoin X (henselianLevel L : Set Ωx), y ∈ D := by
    intro y hy
    have hcl : Submonoid.closure (henselianLevel L : Set Ωx) = (henselianLevel L).toSubmonoid :=
      Submonoid.closure_eq _
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun z _ => Algebra.IsAlgebraic.isAlgebraic z),
      ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span,
      hcl] at hy
    refine (Submodule.span_le.mpr ?_) hy
    intro z hz γ hγ
    exact ⟨z, hz, by simpa using hγ⟩
  exact hspan x (le_adjoin_henselianLevel hr L hx) γ hγ

end Density

end Langlands.Henniart.Laumon
