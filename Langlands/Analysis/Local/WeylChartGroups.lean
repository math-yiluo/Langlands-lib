import Langlands.Analysis.Local.WeylChartMeasures
import Langlands.Analysis.Local.QuotientMeasure

/-! # Group coordinates near a regular unit: the torus, its cosets and the orbit map -/

noncomputable section

namespace Langlands.Analysis.WeylChart

open Metric Set Topology MeasureTheory Measure Langlands.QuotientIntegration
open scoped NNReal ENNReal

universe u v

variable {F : Type u} [NontriviallyNormedField F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R]

section Algebra

open scoped Classical in
/-- The unit with a given value, and `1` for a non-unit. -/
def unitOf (a : R) : Rˣ :=
  if h : IsUnit a then h.unit else 1

theorem val_unitOf {a : R} (h : IsUnit a) : ((unitOf a : Rˣ) : R) = a := by
  simp [unitOf, h]

theorem unitOf_of_not_isUnit {a : R} (h : ¬ IsUnit a) : unitOf a = 1 := by
  simp [unitOf, h]

/-- The centralizer of a unit in the group of units. -/
abbrev torusGroup (γ : Rˣ) : Subgroup Rˣ :=
  Subgroup.centralizer {γ}

theorem mem_torusGroup_iff {γ u : Rˣ} : u ∈ torusGroup γ ↔ (u : R) * γ = γ * u := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← Units.val_mul, ← Units.val_mul, Units.val_inj]

theorem self_mem_torusGroup (γ : Rˣ) : γ ∈ torusGroup γ :=
  Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem unitOf_mem_torusGroup {γ : Rˣ} (s : centralizerAlg F γ) :
    unitOf (1 + (s : R)) ∈ torusGroup γ := by
  rw [mem_torusGroup_iff]
  by_cases h : IsUnit (1 + (s : R))
  · rw [val_unitOf h]
    have hs := (Subalgebra.mem_centralizer_iff F).1 s.property (γ : R) (Set.mem_singleton _)
    rw [add_mul, mul_add, one_mul, mul_one, hs]
  · rw [unitOf_of_not_isUnit h]
    simp

/-- The torus coordinate `s ↦ (1 + s) γ`. -/
def torusChart (γ : Rˣ) (s : centralizerAlg F γ) : torusGroup γ :=
  ⟨unitOf (1 + (s : R)), unitOf_mem_torusGroup s⟩ * ⟨γ, self_mem_torusGroup γ⟩

/-- The coset coordinate `y ↦ T (1 + y)⁻¹`. -/
def cosetChart (γ : Rˣ) (y : LinearMap.range (defect F γ)) : LeftQuotient (torusGroup γ) :=
  leftQuotientMap (torusGroup γ) (unitOf (1 + (y : R)))⁻¹

/-- The coordinates of the source of the orbit map. -/
def orbitCoord (γ : Rˣ) (x : Coord F γ) : LeftQuotient (torusGroup γ) × torusGroup γ :=
  (cosetChart γ x.1, torusChart γ x.2)

/-- The orbit map `(H x, h) ↦ x⁻¹ h x` for a commutative subgroup `H`. -/
def orbitMap {H : Subgroup Rˣ} (hcomm : ∀ a b : H, a * b = b * a) :
    LeftQuotient H × H → Rˣ :=
  fun p => descend H (fun g => g⁻¹ * (p.2 : Rˣ) * g) (fun k g => by
    have h := congrArg Subtype.val (hcomm k p.2)
    simp only [Subgroup.coe_mul] at h
    calc (k.val * g)⁻¹ * (p.2 : Rˣ) * (k.val * g) = g⁻¹ * (k.val⁻¹ * ((p.2 : Rˣ) * k.val)) * g := by
          group
      _ = g⁻¹ * (p.2 : Rˣ) * g := by rw [← h]; group) p.1

theorem orbitMap_mk {H : Subgroup Rˣ} (hcomm : ∀ a b : H, a * b = b * a) (g : Rˣ)
    (h : H) : orbitMap hcomm (leftQuotientMap H g, h) = g⁻¹ * (h : Rˣ) * g :=
  rfl

end Algebra

end Langlands.Analysis.WeylChart
