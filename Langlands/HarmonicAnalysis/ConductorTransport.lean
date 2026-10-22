import Langlands.HarmonicAnalysis.Conductor
import Langlands.HarmonicAnalysis.FieldTransport
import Langlands.LocalField.CanonicalTransport

/-! # Character conductors under a p-adic algebra equivalence -/

noncomputable section

namespace Langlands.PadicField.ConductorTransport

open HarmonicAnalysis

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (e : F.Carrier ≃ₐ[Padic p] E.Carrier)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : NontriviallyNormedField E.Carrier := E.canonicalNormedField
local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : TopologicalSpace E.Carrier := E.canonicalTopologicalData.topology

/-- The actual algebra equivalence on unit groups, with canonical topologies. -/
def unitsEquiv : F.Carrierˣ ≃ₜ* E.Carrierˣ where
  toMulEquiv := Units.mapEquiv e.toMulEquiv
  continuous_toFun := (Weil.Local.extension_isometry F E e.toAlgHom).continuous.units_map _
  continuous_invFun := (Weil.Local.extension_isometry E F e.symm.toAlgHom).continuous.units_map _

@[simp] theorem unitsEquiv_apply (x : F.Carrierˣ) :
    (unitsEquiv F E e x : E.Carrier) = e (x : F.Carrier) := rfl

@[simp] theorem unitsEquiv_symm_apply (y : E.Carrierˣ) :
    ((unitsEquiv F E e).symm y : F.Carrier) = e.symm (y : E.Carrier) := rfl

/-- Inverse pullback along the actual field equivalence. -/
def additiveCharacter (ψ : UnitaryAdditiveCharacter F.Carrier) :
    UnitaryAdditiveCharacter E.Carrier :=
  FieldTransport.additiveCharacter e.toRingEquiv
    (Weil.Local.extension_isometry E F e.symm.toAlgHom).continuous ψ

@[simp] theorem additiveCharacter_apply (ψ : UnitaryAdditiveCharacter F.Carrier)
    (y : E.Carrier) : additiveCharacter F E e ψ y = ψ (e.symm y) := rfl

/-- Inverse pullback of an actual continuous quasicharacter on the unit group. -/
def quasicharacter (χ : Quasicharacter F.Carrier) : Quasicharacter E.Carrier :=
  χ.comp (ContinuousMonoidHom.toContinuousMonoidHom (unitsEquiv F E e).symm)

@[simp] theorem quasicharacter_apply (χ : Quasicharacter F.Carrier) (y : E.Carrierˣ) :
    quasicharacter F E e χ y = χ ((unitsEquiv F E e).symm y) := rfl

/-- The canonical valuation lattices have exactly the same integer indices. -/
theorem mem_additiveLattice_map_iff (n : ℤ) (x : F.Carrier) :
    e x ∈ E.canonicalTopologicalData.additiveLattice n ↔
      x ∈ F.canonicalTopologicalData.additiveLattice n := by
  simp only [TopologicalData.mem_additiveLattice, CanonicalTransport.discreteValuation_map]

/-- The actual unit filtration is preserved, including integral units at level zero. -/
theorem mem_principalUnits_map_iff (n : ℕ) (x : F.Carrierˣ) :
    unitsEquiv F E e x ∈ E.canonicalTopologicalData.principalUnits n ↔
      x ∈ F.canonicalTopologicalData.principalUnits n := by
  simp only [TopologicalData.mem_principalUnits, unitsEquiv_apply,
    ← map_one e, ← map_sub e, CanonicalTransport.discreteValuation_map]

/-- Triviality on the full additive lattice is preserved and reflected. -/
theorem additiveTrivialAt_iff (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℤ) :
    E.canonicalTopologicalData.AdditiveTrivialAt (additiveCharacter F E e ψ) n ↔
      F.canonicalTopologicalData.AdditiveTrivialAt ψ n := by
  constructor
  · intro h x hx
    have h' := h (e x) ((mem_additiveLattice_map_iff F E e n x).2 hx)
    simpa only [additiveCharacter_apply, e.symm_apply_apply] using h'
  · intro h y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [additiveCharacter_apply, e.symm_apply_apply] using
      h x ((mem_additiveLattice_map_iff F E e n x).1 hy)

/-- The greatest additive triviality level is independent of the field presentation. -/
theorem additiveConductor_eq (ψ : UnitaryAdditiveCharacter F.Carrier) :
    E.canonicalTopologicalData.additiveConductor (additiveCharacter F E e ψ) =
      F.canonicalTopologicalData.additiveConductor ψ := by
  apply le_antisymm
  · apply (F.canonicalTopologicalData.additiveConductor_spec ψ).2
    exact (additiveTrivialAt_iff F E e ψ _).1
      (E.canonicalTopologicalData.additiveConductor_spec _).1
  · apply (E.canonicalTopologicalData.additiveConductor_spec _).2
    exact (additiveTrivialAt_iff F E e ψ _).2
      (F.canonicalTopologicalData.additiveConductor_spec ψ).1

/-- Triviality on the full principal-unit group is preserved and reflected. -/
theorem multiplicativeTrivialAt_iff (χ : Quasicharacter F.Carrier) (n : ℕ) :
    E.canonicalTopologicalData.MultiplicativeTrivialAt (quasicharacter F E e χ) n ↔
      F.canonicalTopologicalData.MultiplicativeTrivialAt χ n := by
  constructor
  · intro h x hx
    have h' := h (unitsEquiv F E e x) ((mem_principalUnits_map_iff F E e n x).2 hx)
    simpa only [quasicharacter_apply, ContinuousMulEquiv.symm_apply_apply] using h'
  · intro h y hy
    obtain ⟨x, rfl⟩ := (unitsEquiv F E e).surjective y
    simpa only [quasicharacter_apply, ContinuousMulEquiv.symm_apply_apply] using
      h x ((mem_principalUnits_map_iff F E e n x).1 hy)

/-- The least principal-unit triviality level is independent of the field presentation. -/
theorem multiplicativeConductor_eq (χ : Quasicharacter F.Carrier) :
    E.canonicalTopologicalData.multiplicativeConductor (quasicharacter F E e χ) =
      F.canonicalTopologicalData.multiplicativeConductor χ := by
  apply le_antisymm
  · apply (E.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le _ _).1
    exact (multiplicativeTrivialAt_iff F E e χ _).2
      (F.canonicalTopologicalData.multiplicativeConductor_spec χ)
  · apply (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le _ _).1
    exact (multiplicativeTrivialAt_iff F E e χ _).1
      (E.canonicalTopologicalData.multiplicativeConductor_spec _)

/-- Unramifiedness is preserved and reflected by the same character pullback. -/
theorem isUnramifiedQuasicharacter_iff (χ : Quasicharacter F.Carrier) :
    E.canonicalTopologicalData.IsUnramifiedQuasicharacter (quasicharacter F E e χ) ↔
      F.canonicalTopologicalData.IsUnramifiedQuasicharacter χ := by
  rw [← E.canonicalTopologicalData.multiplicativeConductor_eq_zero_iff,
    ← F.canonicalTopologicalData.multiplicativeConductor_eq_zero_iff,
    multiplicativeConductor_eq]

end Langlands.PadicField.ConductorTransport
