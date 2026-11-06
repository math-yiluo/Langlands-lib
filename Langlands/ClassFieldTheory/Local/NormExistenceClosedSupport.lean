import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof
import Mathlib.Topology.Algebra.Group.Subgroup

/-! # Closedness of actual local norm subgroups -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

open Langlands.LocalClassField

/-- Closedness of the actual norm subgroup for arbitrary finite local
extensions, with independently chosen field universes and supplied topologies. -/
def ClosedLocalNormSubgroups : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (_S : E.TopologicalData),
    letI := T.topology
    IsClosed (normSubgroup F.Carrier E.Carrier : Set F.Carrierˣ)

/-- A subgroup is closed if its intersection with an open subgroup is closed. -/
theorem isClosed_subgroup_of_isClosed_inter_openSubgroup
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N U : Subgroup G) (hU : IsOpen (U : Set G))
    (hNU : IsClosed ((N : Set G) ∩ (U : Set G))) : IsClosed (N : Set G) := by
  have hsmall : N.topologicalClosure ⊓ U ≤ N := by
    intro x hx
    exact (hNU.closure_eq ▸ hU.closure_inter hx).1
  apply isClosed_of_closure_subset
  intro x hx
  let V : Set G := (fun y : G => x⁻¹ * y) ⁻¹' (U : Set G)
  have hV : IsOpen V := hU.preimage (continuous_const.mul continuous_id)
  have hxV : x ∈ V := by simp [V]
  obtain ⟨y, hyV, hyN⟩ := mem_closure_iff_nhds.mp hx V (hV.mem_nhds hxV)
  have hyU : y⁻¹ * x ∈ U := by simpa using U.inv_mem hyV
  have hyQ : y ∈ N.topologicalClosure := N.le_topologicalClosure hyN
  have hxyN := hsmall ⟨N.topologicalClosure.mul_mem
    (N.topologicalClosure.inv_mem hyQ) hx, hyU⟩
  simpa using N.mul_mem hyN hxyN

variable {p : ℕ} [Fact p.Prime]

/-- The actual integral-unit subgroup is open for the supplied topology. -/
theorem isOpen_unitSubgroup (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    IsOpen (T.unitSubgroup : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let v := ValuativeRel.valuation F.Carrier
  have he : (T.unitSubgroup : Set F.Carrierˣ) =
      (fun x : F.Carrierˣ => (x : F.Carrier)) ⁻¹' {x | v.restrict x = 1} := by
    ext x
    exact (Valuation.mem_unitGroup_iff F.Carrier v x).trans v.restrict_eq_one_iff.symm
  rw [he]
  exact (v.isOpen_sphere one_ne_zero).preimage Units.continuous_val

/-- Integral units are exactly the units of normalized order zero. -/
theorem mem_unitSubgroup_iff_ord_eq_zero
    (F : PadicField.{u} p) (T : F.TopologicalData) (a : F.Carrierˣ) :
    a ∈ T.unitSubgroup ↔ T.ord (a : F.Carrier) = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  constructor
  · intro ha
    have hv := (Valuation.mem_unitGroup_iff F.Carrier
      (ValuativeRel.valuation F.Carrier) a).mp ha
    change -WithZero.log ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier (a : F.Carrier))) = 0
    simp [hv]
  · intro ha
    rw [← T.unitFiltration_zero]
    exact T.mem_unitFiltration_zero_of_ord_eq_zero a ha

/-- The norm group near one is the compact image of the integral units above. -/
theorem normSubgroup_inter_unitSubgroup_eq_image
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData) :
    ((normSubgroup F.Carrier E.Carrier : Set F.Carrierˣ) ∩ T.unitSubgroup) =
      (normUnits F.Carrier E.Carrier) '' (S.unitSubgroup : Set E.Carrierˣ) := by
  ext a
  constructor
  · rintro ⟨⟨b, rfl⟩, hb⟩
    refine ⟨b, ?_, rfl⟩
    apply (mem_unitSubgroup_iff_ord_eq_zero E S b).mpr
    apply (ord_relative_norm_units_eq_zero_iff F E T S b).mp
    exact (mem_unitSubgroup_iff_ord_eq_zero F T _).mp hb
  · rintro ⟨b, hb, rfl⟩
    refine ⟨⟨b, rfl⟩, ?_⟩
    apply (mem_unitSubgroup_iff_ord_eq_zero F T _).mpr
    apply (ord_relative_norm_units_eq_zero_iff F E T S b).mpr
    exact (mem_unitSubgroup_iff_ord_eq_zero E S b).mp hb

/-- The determinant-norm subgroup of any finite extension is closed. -/
theorem isClosed_normSubgroup
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData) :
    letI := T.topology
    IsClosed (normSubgroup F.Carrier E.Carrier : Set F.Carrierˣ) := by
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  apply isClosed_subgroup_of_isClosed_inter_openSubgroup
    (normSubgroup F.Carrier E.Carrier) T.unitSubgroup (isOpen_unitSubgroup F T)
  rw [normSubgroup_inter_unitSubgroup_eq_image F E T S]
  have hS : IsCompact (S.unitSubgroup : Set E.Carrierˣ) := by
    rw [← S.unitFiltration_zero]
    exact S.isCompact_unitFiltration 0
  exact (hS.image (localNorm T S).continuous).isClosed

/-- Closedness follows from the compact integral units and the norm-order law. -/
theorem closedLocalNormSubgroups : ClosedLocalNormSubgroups.{u, v} := by
  intro p hp F E hA hTower hFin T S
  exact isClosed_normSubgroup F E T S

end Langlands.ClassFieldTheory.Local
