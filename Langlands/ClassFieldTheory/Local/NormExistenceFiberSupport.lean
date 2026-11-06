import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof
import Mathlib.Topology.Compactness.Compact

/-! # Compact fibers for actual local norms and power maps -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- Compactness of every norm fiber and every nonzero power fiber. -/
def CompactLocalNormAndPowerFibers : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    letI := S.topology
    (∀ a : F.Carrierˣ, IsCompact ((Langlands.LocalClassField.localNorm T S) ⁻¹' {a})) ∧
    ∀ (n : ℕ), n ≠ 0 → ∀ a : E.Carrierˣ,
      IsCompact ((fun x : E.Carrierˣ => x ^ n) ⁻¹' {a})

/-- A continuous group homomorphism has compact fibers if its kernel lies
in a compact subgroup of the source. -/
theorem isCompact_fiber_of_kernel_le
    {G : Type u} {H : Type v} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [T2Space H]
    (f : G →ₜ* H) (U : Subgroup G) (hU : IsCompact (U : Set G))
    (hker : f.toMonoidHom.ker ≤ U) (a : H) : IsCompact (f ⁻¹' {a}) := by
  by_cases hne : (f ⁻¹' {a}).Nonempty
  · obtain ⟨b, hb⟩ := hne
    have hb' : f b = a := hb
    refine (hU.image (continuous_const.mul continuous_id :
      Continuous (fun x : G => b * x))).of_isClosed_subset
        (isClosed_singleton.preimage f.continuous) ?_
    intro x hx
    have hx' : f x = a := hx
    refine ⟨b⁻¹ * x, hker ?_, by simp⟩
    change f (b⁻¹ * x) = 1
    simp [hb', hx']
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isCompact_empty

/-- Compact-fiber lifting through a nonempty downward directed family of
closed subgroups. -/
theorem exists_universal_preimage_of_compact_fiber
    {G : Type u} {H : Type v} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [T2Space H]
    (f : G →ₜ* H) (𝒩 : Set (Subgroup G)) (hne : 𝒩.Nonempty)
    (hdir : DirectedOn (· ≥ ·) 𝒩)
    (hclosed : ∀ N ∈ 𝒩, IsClosed (N : Set G))
    (a : H) (hfiber : IsCompact (f ⁻¹' {a}))
    (ha : ∀ N ∈ 𝒩, a ∈ N.map f.toMonoidHom) :
    ∃ b : G, f b = a ∧ ∀ N ∈ 𝒩, b ∈ N := by
  let : Nonempty 𝒩 := hne.to_subtype
  let C (N : 𝒩) : Set G := (N.1 : Set G) ∩ f ⁻¹' {a}
  have hc : ∀ N : 𝒩, IsClosed (C N) := fun N =>
    (hclosed N.1 N.2).inter (isClosed_singleton.preimage f.continuous)
  have hd : Directed (· ⊇ ·) C := by
    intro N M
    obtain ⟨L, hL, hLN, hLM⟩ := hdir N.1 N.2 M.1 M.2
    exact ⟨⟨L, hL⟩, fun _ hx => ⟨hLN hx.1, hx.2⟩,
      fun _ hx => ⟨hLM hx.1, hx.2⟩⟩
  have hn : ∀ N : 𝒩, (C N).Nonempty := by
    intro N
    obtain ⟨b, hb, hab⟩ := ha N.1 N.2
    exact ⟨b, hb, hab⟩
  have hk : ∀ N : 𝒩, IsCompact (C N) := fun N =>
    hfiber.of_isClosed_subset (hc N) (fun _ hx => hx.2)
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    C hd hn hk hc
  have hbN : ∀ N : 𝒩, b ∈ C N := Set.mem_iInter.mp hb
  obtain ⟨N, hN⟩ := hne
  exact ⟨b, (hbN ⟨N, hN⟩).2, fun M hM => (hbN ⟨M, hM⟩).1⟩

open Langlands.LocalClassField

variable {p : ℕ} [Fact p.Prime]

/-- Every fiber of the actual determinant norm is compact in the supplied
multiplicative local-field topology. -/
theorem isCompact_localNorm_fiber
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData) (a : F.Carrierˣ) :
    letI := T.topology
    letI := S.topology
    IsCompact ((localNorm T S) ⁻¹' {a}) := by
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  let := T.fieldT2
  let := S.fieldT2
  let : FiniteDimensional F.Carrier E.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  have hU : IsCompact (S.unitSubgroup : Set E.Carrierˣ) := by
    rw [← S.unitFiltration_zero]
    exact S.isCompact_unitFiltration 0
  apply isCompact_fiber_of_kernel_le (localNorm T S) S.unitSubgroup hU
  intro x hx
  have hx' : normUnits F.Carrier E.Carrier x = 1 := hx
  have ho : S.ord (x : E.Carrier) = 0 := by
    apply (ord_relative_norm_units_eq_zero_iff F E T S x).mp
    change T.ord (normUnits F.Carrier E.Carrier x : F.Carrier) = 0
    rw [hx']
    exact T.ord_one
  rw [← S.unitFiltration_zero]
  exact S.mem_unitFiltration_zero_of_ord_eq_zero x ho

/-- Nonzero power maps have compact fibers in the supplied multiplicative
topology of a p-adic field. -/
theorem isCompact_power_fiber
    (F : PadicField.{u} p) (T : F.TopologicalData) (n : ℕ) (hn : n ≠ 0)
    (a : F.Carrierˣ) :
    letI := T.topology
    IsCompact ((fun x : F.Carrierˣ => x ^ n) ⁻¹' {a}) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let f : F.Carrierˣ →ₜ* F.Carrierˣ :=
    { powMonoidHom n with continuous_toFun := continuous_id.pow n }
  have hU : IsCompact (T.unitSubgroup : Set F.Carrierˣ) := by
    rw [← T.unitFiltration_zero]
    exact T.isCompact_unitFiltration 0
  apply isCompact_fiber_of_kernel_le f T.unitSubgroup hU
  intro x hx
  have hx' : x ^ n = 1 := hx
  have ho : T.ord (x : F.Carrier) = 0 := by
    have h : (n : ℤ) * T.ord (x : F.Carrier) = 0 := by
      rw [← T.ord_zpow, zpow_natCast]
      change T.ord ((x ^ n : F.Carrierˣ) : F.Carrier) = 0
      rw [hx']
      exact T.ord_one
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)
  rw [← T.unitFiltration_zero]
  exact T.mem_unitFiltration_zero_of_ord_eq_zero x ho

/-- The complete compact-fiber assertion. -/
theorem compactLocalNormAndPowerFibers : CompactLocalNormAndPowerFibers.{u, v} := by
  intro p hp F E hFE htower T S
  exact ⟨isCompact_localNorm_fiber F E T S, isCompact_power_fiber E S⟩

end Langlands.ClassFieldTheory.Local
