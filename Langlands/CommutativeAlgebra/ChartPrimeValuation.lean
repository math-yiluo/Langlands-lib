import Langlands.CommutativeAlgebra.ChartUniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! # The valuation of a prime element of a factorial chart -/

noncomputable section

namespace Langlands.CommutativeAlgebra.ChartUniqueFactorization

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

omit [IsDomain A] in
theorem mem_chartLoc {S : Subalgebra A K} {Q : Ideal S} [Q.IsPrime] {x : K} :
    x ∈ chartLoc K S Q ↔ ∃ a s : S, s ∉ Q ∧ x = (a : K) * (s : K)⁻¹ :=
  ⟨fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩, fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩⟩

omit [IsDomain A] in
/-- Elements of a chart outside a prime are units of its localization. -/
theorem mem_chartLoc_of_notMem {S : Subalgebra A K} {Q : Ideal S} [Q.IsPrime] {s : S}
    (hs : s ∉ Q) : (s : K) ∈ chartLoc K S Q ∧ (s : K)⁻¹ ∈ chartLoc K S Q := by
  have hs0 : (s : K) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := Subtype.ext h
    rw [this]
    exact Q.zero_mem
  exact ⟨mem_chartLoc.2 ⟨s, 1, fun h => Q.ne_top_iff_one.1 (Ideal.IsPrime.ne_top ‹_›) h,
      by simp⟩, mem_chartLoc.2 ⟨1, s, hs, by simp⟩⟩

omit [IsDomain A] in
/-- The inverse of a nonzero element of a prime is not in the localization at that prime. -/
theorem inv_notMem_chartLoc {S : Subalgebra A K} {Q : Ideal S} [Q.IsPrime] {π : S} (hπ : π ∈ Q)
    (hπ0 : (π : K) ≠ 0) : (π : K)⁻¹ ∉ chartLoc K S Q := by
  rintro ⟨a, s, hs, h⟩
  apply hs
  have h' : (s : K) = (π : K) * (a : K) := by
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := Subtype.ext h0
      rw [this]
      exact Q.zero_mem
    change (π : K)⁻¹ = (a : K) * (s : K)⁻¹ at h
    field_simp at h
    linear_combination h
  have : s = π * a := Subtype.ext (by rw [h']; rfl)
  rw [this]
  exact Q.mul_mem_right a hπ

variable {S : Subalgebra A K} [UniqueFactorizationMonoid S]

/-- **Valuation of a prime element.** In a factorial chart with a prime element `π`, every
nonzero rational function is a power of `π` times a unit of the localization at `(π)`. -/
theorem exists_zpow_mul_unit {π : S} (hπ : Prime π) [(Ideal.span {π}).IsPrime] {x : K}
    (hx : x ≠ 0) :
    ∃ n : ℤ, x * (π : K) ^ (-n) ∈ chartLoc K S (Ideal.span {π}) ∧
      (x * (π : K) ^ (-n))⁻¹ ∈ chartLoc K S (Ideal.span {π}) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hinj := IsFractionRing.injective A K
  have hS : ∀ c : A, c ≠ 0 → algebraMap A S c ≠ 0 := by
    intro c hc h0
    apply hc
    apply hinj
    rw [map_zero]
    exact congrArg Subtype.val h0
  obtain ⟨i, a', ha'd, ha'⟩ := WfDvdMonoid.max_power_factor (hS a ha0) hπ.irreducible
  obtain ⟨j, b', hb'd, hb'⟩ := WfDvdMonoid.max_power_factor (hS b hb0) hπ.irreducible
  have hπ0 : (π : K) ≠ 0 := by
    intro h0
    exact hπ.ne_zero (Subtype.ext h0)
  have ha'Q : a' ∉ Ideal.span {π} := by rwa [Ideal.mem_span_singleton]
  have hb'Q : b' ∉ Ideal.span {π} := by rwa [Ideal.mem_span_singleton]
  have hb'0 : (b' : K) ≠ 0 := by
    intro h0
    apply hb'Q
    have : b' = 0 := Subtype.ext h0
    rw [this]
    exact Ideal.zero_mem _
  have ha'0 : (a' : K) ≠ 0 := by
    intro h0
    apply ha'Q
    have : a' = 0 := Subtype.ext h0
    rw [this]
    exact Ideal.zero_mem _
  have hxa : algebraMap A K a = (π : K) ^ i * (a' : K) := by
    have := congrArg Subtype.val ha'
    simpa using this
  have hxb : algebraMap A K b = (π : K) ^ j * (b' : K) := by
    have := congrArg Subtype.val hb'
    simpa using this
  have key : IsLocalization.mk' K a b * (π : K) ^ (-((i : ℤ) - j)) = (a' : K) * (b' : K)⁻¹ := by
    rw [IsFractionRing.mk'_eq_div, hxa, hxb, zpow_neg, zpow_sub₀ hπ0, zpow_natCast,
      zpow_natCast]
    field_simp
  refine ⟨(i : ℤ) - j, ?_, ?_⟩
  · rw [key]
    exact mem_chartLoc.2 ⟨a', b', hb'Q, rfl⟩
  · rw [key, mul_inv, inv_inv, mul_comm]
    exact mem_chartLoc.2 ⟨b', a', ha'Q, rfl⟩

end Langlands.CommutativeAlgebra.ChartUniqueFactorization
