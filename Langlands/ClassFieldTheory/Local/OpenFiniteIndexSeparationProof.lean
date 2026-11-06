import Langlands.ClassFieldTheory.Local.OpenFiniteIndexSeparationStatement
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport
import Langlands.ClassFieldTheory.Local.NormCorrespondenceStatement
import Langlands.ClassFieldTheory.Local.NormStatement
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.LocalField.Uniformizer
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

noncomputable section

open scoped WithZero
open Topology

namespace Langlands.PadicField.TopologicalData

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

theorem mem_unitSubgroup_iff_orderHom (x : F.Carrierˣ) :
    x ∈ T.unitSubgroup ↔ T.orderHom x = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [Valuation.mem_unitGroup_iff]
  change _ = 1 ↔ Multiplicative.ofAdd (-WithZero.log (T.discreteValuation x)) = 1
  rw [ofAdd_eq_one, neg_eq_zero]
  have hn : T.discreteValuation x ≠ 0 :=
    T.discreteValuation.ne_zero_iff.mpr x.ne_zero
  have hlog : WithZero.log (T.discreteValuation x) = 0 ↔ T.discreteValuation x = 1 := by
    rw [← WithZero.exp_eq_one, WithZero.exp_log hn]
  rw [hlog]
  change _ = 1 ↔
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier x) = 1
  exact ⟨fun h => by rw [h, map_one], fun h =>
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).injective
      (h.trans (map_one _).symm)⟩

theorem integerUnitsInclusion_isOpenEmbedding :
    let := T.topology
    Topology.IsOpenEmbedding T.integerUnitsInclusion := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  refine ⟨⟨Topology.IsInducing.units_map Topology.IsInducing.subtypeVal,
    T.integerUnitsInclusion_injective⟩, ?_⟩
  have hrange : Set.range T.integerUnitsInclusion = (T.unitSubgroup : Set F.Carrierˣ) := by
    rw [← T.unitFiltration_zero]
    ext x
    simp [unitFiltration, T.congruenceUnits_zero]
  rw [hrange]
  exact (Langlands.ClassFieldTheory.Local.isOpen_unitSubgroup F T)

theorem isOpen_unitFiltration (n : ℕ) :
    let := T.topology
    IsOpen (T.unitFiltration n : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have : Finite (T.TruncatedIntegers n) := inferInstance
  have : (T.congruenceUnits n).FiniteIndex :=
    Subgroup.finiteIndex_ker (T.truncatedUnitsReduction n)
  exact T.integerUnitsInclusion_isOpenEmbedding.isOpenMap _
    ((T.congruenceUnits n).isOpen_of_isClosed_of_finiteIndex
      (T.isClosed_congruenceUnits n))

theorem exists_open_finiteIndex_excluding_of_mem_unitSubgroup
    (a : F.Carrierˣ) (ha : a ≠ 1) (haU : a ∈ T.unitSubgroup) :
    let := T.topology
    ∃ H : Subgroup F.Carrierˣ, IsOpen (H : Set F.Carrierˣ) ∧ H.FiniteIndex ∧ a ∉ H := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let π := LocalFactor.PadicAbelian.uniformizerUnit T
  have hπ : T.orderHom π = Multiplicative.ofAdd (1 : ℤ) :=
    congrArg Multiplicative.ofAdd (LocalFactor.PadicAbelian.uniformizerUnit_ord T)
  let s : Multiplicative ℤ →* F.Carrierˣ := zpowersHom _ π
  have hs (z : Multiplicative ℤ) : T.orderHom (s z) = z := by
    change T.orderHom (π ^ z.toAdd) = z
    rw [map_zpow, hπ]
    change Multiplicative.ofAdd (z.toAdd • (1 : ℤ)) = z
    simp
  let r : F.Carrierˣ →* F.Carrierˣ := (MonoidHom.id _) / (s.comp T.orderHom)
  have hr (x : F.Carrierˣ) : r x ∈ T.unitSubgroup := by
    apply (T.mem_unitSubgroup_iff_orderHom _).mpr
    change T.orderHom (x / s (T.orderHom x)) = 1
    rw [map_div, hs, div_self']
  have hrfix (x : F.Carrierˣ) (hx : x ∈ T.unitSubgroup) : r x = x := by
    change x / s (T.orderHom x) = x
    rw [(T.mem_unitSubgroup_iff_orderHom x).mp hx, map_one, div_one]
  let rU : F.Carrierˣ →* T.Integersˣ :=
    T.integerUnitsEquiv.toMonoidHom.comp (r.codRestrict T.unitSubgroup hr)
  have hrU (x : F.Carrierˣ) : T.integerUnitsInclusion (rU x) = r x := by
    apply Units.ext
    rfl
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ∉ T.unitFiltration n := by
    by_contra! h
    exact ha (T.unitFiltration_separated a h)
  let f : F.Carrierˣ →* (T.TruncatedIntegers n)ˣ :=
    (T.truncatedUnitsReduction n).comp rU
  have hle : T.unitFiltration n ≤ f.ker := by
    rintro x ⟨y, hy, rfl⟩
    have hx : T.integerUnitsInclusion y ∈ T.unitSubgroup :=
      T.unitFiltration_zero ▸ T.unitFiltration_antitone (Nat.zero_le n)
        (show T.integerUnitsInclusion y ∈ T.unitFiltration n from ⟨y, hy, rfl⟩)
    have heq : rU (T.integerUnitsInclusion y) = y :=
      T.integerUnitsInclusion_injective ((hrU _).trans (hrfix _ hx))
    change T.truncatedUnitsReduction n (rU (T.integerUnitsInclusion y)) = 1
    rw [heq]
    exact hy
  refine ⟨f.ker, Subgroup.isOpen_mono hle (T.isOpen_unitFiltration n),
    Subgroup.finiteIndex_ker f, ?_⟩
  intro h
  apply hn
  refine ⟨rU a, h, ?_⟩
  exact (hrU a).trans (hrfix a haU)

theorem exists_open_finiteIndex_excluding_of_not_mem_unitSubgroup
    (a : F.Carrierˣ) (haU : a ∉ T.unitSubgroup) :
    let := T.topology
    ∃ H : Subgroup F.Carrierˣ, IsOpen (H : Set F.Carrierˣ) ∧ H.FiniteIndex ∧ a ∉ H := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let n := (T.ord a).natAbs + 1
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let f : F.Carrierˣ →* Multiplicative (ZMod n) :=
    (Int.castAddHom (ZMod n)).toMultiplicative.comp T.orderHom
  have hle : T.unitSubgroup ≤ f.ker := by
    intro x hx
    change (Int.castAddHom (ZMod n)).toMultiplicative (T.orderHom x) = 1
    rw [(T.mem_unitSubgroup_iff_orderHom x).mp hx, map_one]
  refine ⟨f.ker, Subgroup.isOpen_mono hle (Langlands.ClassFieldTheory.Local.isOpen_unitSubgroup F T),
    Subgroup.finiteIndex_ker f, ?_⟩
  intro h
  change Multiplicative.ofAdd ((T.ord a : ℤ) : ZMod n) = 1 at h
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (T.ord a) n).mp (ofAdd_eq_one.mp h)
  have hz : T.ord a = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by
    rw [Int.natAbs_natCast]
    exact Nat.lt_succ_self _)
  apply haU
  apply (T.mem_unitSubgroup_iff_orderHom a).mpr
  change Multiplicative.ofAdd (T.ord a) = 1
  simp [hz]

theorem exists_open_finiteIndex_excluding (a : F.Carrierˣ) (ha : a ≠ 1) :
    let := T.topology
    ∃ H : Subgroup F.Carrierˣ, IsOpen (H : Set F.Carrierˣ) ∧ H.FiniteIndex ∧ a ∉ H := by
  by_cases haU : a ∈ T.unitSubgroup
  · exact T.exists_open_finiteIndex_excluding_of_mem_unitSubgroup a ha haU
  · exact T.exists_open_finiteIndex_excluding_of_not_mem_unitSubgroup a haU

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField

universe u

/-- The actual local multiplicative group is separated by open finite-index subgroups. -/
theorem openFiniteIndexSubgroupsSeparatePoints : OpenFiniteIndexSubgroupsSeparatePoints.{u} := by
  intro p hp F T
  exact fun a ha => T.exists_open_finiteIndex_excluding a ha

/-- Arithmetic norm existence converts the proved topology separation into norm separation. -/
theorem normSubgroupsSeparatePoints_of_normSubgroupExistence
    (hExist : NormSubgroupExistence.{u}) : NormSubgroupsSeparatePoints.{u} := by
  intro p hp F a ha
  let T := F.canonicalTopologicalData
  obtain ⟨H, hOpen, hIndex, haH⟩ := T.exists_open_finiteIndex_excluding a ha
  obtain ⟨E, ⟨hFin, hAb, hNorm⟩, _⟩ := hExist p F H hOpen hIndex
  exact ⟨E, hFin, hAb, hNorm ▸ haH⟩

end Langlands.LocalClassField
