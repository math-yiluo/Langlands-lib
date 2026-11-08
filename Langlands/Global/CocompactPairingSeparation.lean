import Mathlib.Algebra.Group.AddChar
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Nondegeneracy from cocompactness and one-factor approximation -/

noncomputable section

open Set Filter Topology

universe u v

namespace Langlands.Global.CocompactPairingSeparation

variable {K : Type u} [Field K]
variable {R : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Parameters whose pairings with a prescribed set lie in the right half arc. -/
def smallParameters (ψ : AddChar R Circle) (C : Set R) : Set R :=
  {b | ∀ x ∈ C, ψ (b * x) ∈ Circle.centeredArc (Real.pi / 2)}

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- An additive character contained in the right half arc is trivial. -/
theorem eq_one_of_range_mem_arc (χ : AddChar R Circle)
    (hχ : ∀ x, χ x ∈ Circle.centeredArc (Real.pi / 2)) : χ = 1 := by
  apply DFunLike.ext
  intro x
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro n _
  rw [← χ.map_nsmul_eq_pow]
  exact hχ _

theorem isOpen_smallParameters (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (C : Set R) (hC : IsCompact C) : IsOpen (smallParameters ψ C) := by
  let f : C(R × R, Circle) := ⟨fun p => ψ (p.1 * p.2),
    hψ.comp (continuous_fst.mul continuous_snd)⟩
  exact (ContinuousMap.isOpen_setOfPred_mapsTo hC
    (Circle.isOpen_centeredArc (Real.pi / 2))).preimage f.curry.continuous

theorem smallParameters_mem_nhds (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (C : Set R) (hC : IsCompact C) : smallParameters ψ C ∈ 𝓝 0 := by
  apply (isOpen_smallParameters ψ hψ C hC).mem_nhds
  intro x _
  simp only [zero_mul, ψ.map_zero_eq_one]
  exact ⟨0, by simpa using Real.pi_div_two_pos, Circle.exp_zero⟩

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- A small parameter annihilating the field annihilates the whole ring. -/
theorem annihilates_of_small (ι : K →+* R) (ψ : AddChar R Circle)
    (C : Set R) (hcover : ∀ y : R, ∃ k : K, y - ι k ∈ C)
    (b : R) (hb : ∀ k : K, ψ (b * ι k) = 1)
    (hsmall : b ∈ smallParameters ψ C) :
    ∀ y : R, ψ (b * y) = 1 := by
  have h : ψ.mulShift b = 1 := eq_one_of_range_mem_arc _ (by
    intro y
    obtain ⟨k, hk⟩ := hcover y
    change ψ (b * y) ∈ Circle.centeredArc (Real.pi / 2)
    rw [show b * y = b * (y - ι k) + b * ι k by ring,
      ψ.map_add_eq_mul, hb k, mul_one]
    exact hsmall _ hk)
  intro y
  exact DFunLike.congr_fun h y

/-- One-factor approximation makes every nontrivial field-trivial pairing nondegenerate. -/
theorem nondegenerate (ι : K →+* R) (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (htriv : ∀ k : K, ψ (ι k) = 1)
    (C : Set R) (hC : IsCompact C)
    (hcover : ∀ y : R, ∃ k : K, y - ι k ∈ C)
    (hloc : ∀ a : R, a ≠ 0 → ∃ e z : R, e = a * z ∧
      ∀ N ∈ 𝓝 (0 : R), ∃ k : K, k ≠ 0 ∧ ι k * (1 - e) ∈ N) :
    ∀ a : R, (∀ y : R, ψ (a * y) = 1) → a = 0 := by
  intro a ha
  by_contra hzero
  obtain ⟨e, z, he, heapprox⟩ := hloc a hzero
  have heann : ∀ y : R, ψ (e * y) = 1 := by
    intro y
    rw [he, mul_assoc]
    exact ha _
  obtain ⟨k, hk, hksmall⟩ := heapprox (smallParameters ψ C)
    (smallParameters_mem_nhds ψ hψ C hC)
  have hkann : ∀ l : K, ψ ((ι k * (1 - e)) * ι l) = 1 := by
    intro l
    rw [show (ι k * (1 - e)) * ι l =
      ι (k * l) - e * ι (k * l) by rw [map_mul]; ring,
      ψ.map_sub_eq_div, htriv, heann, div_self']
  have hall := annihilates_of_small ι ψ C hcover _ hkann hksmall
  have hunitann : ∀ y : R, ψ (ι k * y) = 1 := by
    intro y
    rw [show ι k * y = (ι k * (1 - e)) * y + e * (ι k * y) by ring,
      ψ.map_add_eq_mul, hall, heann, one_mul]
  apply hne
  apply DFunLike.ext
  intro y
  change ψ y = 1
  have hki : ι k * ι k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hk, map_one]
  simpa only [← mul_assoc, hki, one_mul] using hunitann (ι k⁻¹ * y)

end Langlands.Global.CocompactPairingSeparation
