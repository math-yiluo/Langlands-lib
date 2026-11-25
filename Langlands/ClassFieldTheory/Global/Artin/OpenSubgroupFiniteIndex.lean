import Langlands.Global.IdeleAbsoluteValue
import Langlands.Global.NormOneIdeleClassCompact
import Langlands.Global.PositiveRealIdeles
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Connected.Basic

/-!
# Open subgroups of the idèle class group have finite index

This file belongs to the Library and uses nothing of the NYLL library. It proves, for a number
field `K`, that every open subgroup `H` of the idèle class group `IdeleClasses K` has finite
index.

The positive reals `ℝ≥0ˣ` embed into the idèle classes through the archimedean places
(`Langlands.Global.PositiveRealIdeles.full`). They form a connected group, so the preimage of the
open, hence closed, subgroup `H` is everything: `H` contains the image of `ℝ≥0ˣ`. That image
meets every fibre of the idèle absolute value (the absolute value of the image of `x` is
`x ^ [K : ℚ]`), so `H` and the norm-one idèle classes `C¹` generate the whole group, and the index
of `H` equals the index of `H ∩ C¹` in `C¹`. The group `C¹` is compact
(`Langlands.Global.NormOneIdeleClass.isCompact_ker_ideleClass`) and `H ∩ C¹` is open in it, so this
index is finite.

## Main declarations

* `connectedSpace_units_nnreal : ConnectedSpace ℝ≥0ˣ`.
* `positiveReal_mem_of_isOpen`: an open subgroup contains the image of `ℝ≥0ˣ`.
* `openSubgroup_finiteIndex K H : H.toSubgroup.FiniteIndex`.

## Sources

Neukirch, *Algebraic Number Theory*, Chapter VI, (1.6) (the norm-one idèle class group is
compact) and (1.8); Milne, *Class Field Theory*, Chapter V, Proposition 4.4.
-/

noncomputable section

universe u

open scoped NNReal

namespace Langlands.ClassFieldTheory.Global.Artin

open Langlands.Global

/-- The group of units of `ℝ≥0`, the positive reals, is connected. -/
theorem connectedSpace_units_nnreal : ConnectedSpace ℝ≥0ˣ := by
  have hset : {g : ℝ≥0 | g ≠ 0} = Set.Ioi 0 := by
    ext g
    simp [pos_iff_ne_zero]
  have : ConnectedSpace {g : ℝ≥0 // g ≠ 0} := by
    have h : IsConnected {g : ℝ≥0 | g ≠ 0} := hset ▸ isConnected_Ioi
    exact isConnected_iff_connectedSpace.mp h
  exact (unitsHomeomorphNeZero (G₀ := ℝ≥0)).symm.surjective.connectedSpace
    (unitsHomeomorphNeZero (G₀ := ℝ≥0)).symm.continuous

section

variable {K : Type u} [Field K] [NumberField K]

/-- An open subgroup of the idèle classes contains the classes of all positive real idèles. -/
theorem positiveReal_mem_of_isOpen (H : OpenSubgroup (IdeleClasses K)) (x : ℝ≥0ˣ) :
    ideleClassMap K (PositiveRealIdeles.full K x) ∈ H := by
  have := connectedSpace_units_nnreal
  let f : ℝ≥0ˣ →ₜ* IdeleClasses K := (ideleClassMap K).comp (PositiveRealIdeles.full K)
  let H₀ : Subgroup ℝ≥0ˣ := H.toSubgroup.comap f.toMonoidHom
  have hopen : IsOpen (H₀ : Set ℝ≥0ˣ) := H.isOpen.preimage f.continuous
  have hclopen : IsClopen (H₀ : Set ℝ≥0ˣ) := ⟨H₀.isClosed_of_isOpen hopen, hopen⟩
  have hall : (H₀ : Set ℝ≥0ˣ) = Set.univ := hclopen.eq_univ ⟨1, H₀.one_mem⟩
  have hx : x ∈ (H₀ : Set ℝ≥0ˣ) := hall ▸ Set.mem_univ x
  exact hx

/-- The positive real whose `[K : ℚ]`-th power is a given positive real. -/
def positiveRoot (K : Type u) [Field K] [NumberField K] (h : ℝ≥0ˣ) : ℝ≥0ˣ :=
  Units.map (NNReal.rpowMonoidHom ((Module.finrank ℚ K : ℝ)⁻¹)) h

theorem positiveRoot_pow (h : ℝ≥0ˣ) : positiveRoot K h ^ Module.finrank ℚ K = h := by
  apply Units.ext
  exact NNReal.rpow_inv_natCast_pow _ Module.finrank_pos.ne'

/-- An open subgroup and the norm-one idèle classes generate the idèle class group. -/
theorem openSubgroup_sup_ker_eq_top (H : OpenSubgroup (IdeleClasses K)) :
    (IdeleAbsoluteValue.ideleClass K).toMonoidHom.ker ⊔ H.toSubgroup = ⊤ := by
  rw [eq_top_iff]
  intro c _
  let y := ideleClassMap K (PositiveRealIdeles.full K
    (positiveRoot K (IdeleAbsoluteValue.ideleClass K c)))
  have hy : y ∈ H := positiveReal_mem_of_isOpen H _
  have hyabs : IdeleAbsoluteValue.ideleClass K y = IdeleAbsoluteValue.ideleClass K c := by
    change IdeleAbsoluteValue.full K (PositiveRealIdeles.full K _) = _
    rw [PositiveRealIdeles.absoluteValue_full, positiveRoot_pow]
  have hker : c * y⁻¹ ∈ (IdeleAbsoluteValue.ideleClass K).toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change IdeleAbsoluteValue.ideleClass K c * (IdeleAbsoluteValue.ideleClass K y)⁻¹ = 1
    rw [hyabs, mul_inv_cancel]
  have hc : c = c * y⁻¹ * y := by group
  rw [hc]
  exact Subgroup.mul_mem_sup hker hy

end

/-- Every open subgroup of the idèle class group of a number field has finite index. -/
theorem openSubgroup_finiteIndex (K : Type u) [Field K] [NumberField K]
    (H : OpenSubgroup (IdeleClasses K)) : H.toSubgroup.FiniteIndex := by
  let C : Subgroup (IdeleClasses K) := (IdeleAbsoluteValue.ideleClass K).toMonoidHom.ker
  have : IsMulCommutative (IdeleClasses K) := IsMulCommutative.of_comm fun a b => mul_comm a b
  have : H.toSubgroup.Normal := Subgroup.normal_of_isMulCommutative _
  have hindex : H.toSubgroup.relIndex C = H.toSubgroup.index := by
    rw [← Subgroup.relIndex_sup_right, openSubgroup_sup_ker_eq_top H, Subgroup.relIndex_top_right]
  have : CompactSpace C := isCompact_iff_compactSpace.mp (NormOneIdeleClass.isCompact_ker_ideleClass K)
  have : Finite (C ⧸ H.toSubgroup.subgroupOf C) :=
    (H.toSubgroup.subgroupOf C).quotient_finite_of_isOpen
      (Subgroup.subgroupOf_isOpen C H.toSubgroup H.isOpen)
  have hfin : (H.toSubgroup.subgroupOf C).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact ⟨hindex ▸ hfin.index_ne_zero⟩

end Langlands.ClassFieldTheory.Global.Artin
