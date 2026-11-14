import Langlands.AllFieldBZ.HarmonicAnalysis.Conductor
import Langlands.AllFieldBZ.LocalField.Definitions
import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof

/-!
# All-field port of `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.HarmonicAnalysis.PadicAdditiveConductorProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped WithZero
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe u
variable {F : LocalFieldPackage.{u}} (T : F.TopologicalData)

private theorem conductor_uniformizer_ne_zero : T.uniformizer ≠ 0 := by
  apply T.discreteValuation.ne_zero_iff.mp
  rw [T.discreteValuation_uniformizer]
  exact WithZero.exp_ne_zero

/-- Membership in the valuation lattice is membership in the actual fractional ideal. -/
theorem mem_additiveLattice_iff_exists_integer (n : ℤ) (x : F.Carrier) :
    x ∈ T.additiveLattice n ↔
      ∃ t : T.Integers, x = T.uniformizer ^ (-n) * (t : F.Carrier) := by
  rw [T.mem_additiveLattice_iff_div_mem_integers]
  have hπ := zpow_ne_zero (-n) T.conductor_uniformizer_ne_zero
  constructor
  · intro hx
    refine ⟨⟨x / T.uniformizer ^ (-n), hx⟩, ?_⟩
    dsimp
    field_simp
  · rintro ⟨t, rfl⟩
    rw [mul_div_cancel_left₀ _ hπ]
    exact t.property

private theorem discreteValuation_eq_exp_neg_ord {a : F.Carrier} (ha : a ≠ 0) :
    T.discreteValuation a = WithZero.exp (-T.ord a) := by
  simp only [Langlands.LocalFieldData.ord, neg_neg]
  exact (WithZero.exp_log (T.discreteValuation.ne_zero_iff.mpr ha)).symm

/-- Multiplication transports the actual valuation lattices with the normalized order. -/
theorem mul_mem_additiveLattice_iff {a : F.Carrier} (ha : a ≠ 0)
    (n : ℤ) (x : F.Carrier) :
    a * x ∈ T.additiveLattice n ↔ x ∈ T.additiveLattice (n + T.ord a) := by
  rw [mem_additiveLattice, mem_additiveLattice, map_mul,
    T.discreteValuation_eq_exp_neg_ord ha, ← le_div_iff₀' WithZero.exp_pos,
    ← WithZero.exp_sub]
  simp only [sub_neg_eq_add]

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- The annihilator of the actual integer ring is the conductor lattice. -/
theorem integer_annihilator_iff_mem_additiveLattice (ψ : AdditiveCharacter)
    (y : F.Carrier) :
    (∀ t : T.Integers, ψ ((t : F.Carrier) * y) = 1) ↔
      y ∈ T.additiveLattice (T.additiveConductor ψ) := by
  constructor
  · intro h
    by_cases hy : y = 0
    · subst y
      exact (T.additiveLattice _).zero_mem
    have htriv : T.AdditiveTrivialAt ψ (-T.ord y) := by
      intro x hx
      have hxO : y⁻¹ * x ∈ T.Integers := by
        apply (T.mem_additiveLattice_zero _).mp
        apply (T.mul_mem_additiveLattice_iff (inv_ne_zero hy) 0 x).mpr
        simpa only [T.ord_inv, zero_add] using hx
      have hh := h ⟨y⁻¹ * x, hxO⟩
      simpa only [mul_right_comm y⁻¹ x y, inv_mul_cancel₀ hy, one_mul] using hh
    have hle := (T.additiveConductor_spec ψ).2 _ htriv
    rw [mem_additiveLattice, T.discreteValuation_eq_exp_neg_ord hy]
    exact WithZero.exp_le_exp.mpr hle
  · intro hy t
    apply (T.additiveConductor_spec ψ).1
    rw [mem_additiveLattice, map_mul]
    calc
      T.discreteValuation (t : F.Carrier) * T.discreteValuation y ≤
          1 * T.discreteValuation y :=
        mul_le_mul_of_nonneg_right
          ((T.mem_integers_iff_discreteValuation_le_one _).mp t.property) zero_le
      _ ≤ WithZero.exp (T.additiveConductor ψ) := by simpa using hy

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.HarmonicAnalysis
universe u

end Langlands.AllFieldBZ.HarmonicAnalysis
