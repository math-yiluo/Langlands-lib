import Langlands.BushnellKutzko.AdjointExactnessProof
import Langlands.BushnellKutzko.TameCorestrictionProof
import Langlands.BushnellKutzko.SubfieldIntegerArithmetic

/-! # Transport of lattice chains between integer rings with equal carriers -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uO' uK uV uF uE

section Congr

variable {O : Type uO} {O' : Type uO'} {K : Type uK} {V : Type uV} [CommRing O] [CommRing O']
  [Field K] [Algebra O K] [Algebra O' K] [AddCommGroup V] [Module K V]
  [Module O V] [IsScalarTower O K V] [Module O' V] [IsScalarTower O' K V]
  {𝓛 : LatticeChain O K V} {𝓛' : LatticeChain O' K V}

theorem mem_adjointLattice_iff_mul {β x : Module.End K V} {k : ℤ} :
    x ∈ adjointLattice 𝓛 β k ↔
      x ∈ 𝓛.endFiltration 0 ∧ β * x - x * β ∈ 𝓛.endFiltration k :=
  Iff.rfl

theorem mem_centralizerLattice_iff_mul {β x : Module.End K V} {k : ℤ} :
    x ∈ centralizerLattice 𝓛 β k ↔ x ∈ 𝓛.endFiltration k ∧ β * x - x * β = 0 :=
  Iff.rfl

namespace LatticeChain

variable (h : ∀ i, (𝓛.lattice i : Set V) = 𝓛'.lattice i)
include h

theorem mem_endFiltration_congr {n : ℤ} {x : Module.End K V} :
    x ∈ 𝓛.endFiltration n ↔ x ∈ 𝓛'.endFiltration n := by
  rw [mem_endFiltration, mem_endFiltration]
  refine forall_congr' fun i => forall_congr' fun v => ?_
  rw [← SetLike.mem_coe, ← SetLike.mem_coe (x := x v), h, h]
  exact Iff.rfl

theorem mem_adjointLattice_congr {β x : Module.End K V} {k : ℤ} :
    x ∈ adjointLattice 𝓛 β k ↔ x ∈ adjointLattice 𝓛' β k := by
  rw [mem_adjointLattice_iff_mul, mem_adjointLattice_iff_mul, mem_endFiltration_congr h,
    mem_endFiltration_congr h]

theorem mem_centralizerLattice_congr {β x : Module.End K V} {k : ℤ} :
    x ∈ centralizerLattice 𝓛 β k ↔ x ∈ centralizerLattice 𝓛' β k := by
  rw [mem_centralizerLattice_iff_mul, mem_centralizerLattice_iff_mul, mem_endFiltration_congr h]

theorem criticalIndexSet_congr (β : Module.End K V) :
    criticalIndexSet 𝓛 β = criticalIndexSet 𝓛' β := by
  ext k
  simp only [criticalIndexSet, Set.mem_ofPred_eq, SetLike.le_def, Submodule.mem_sup,
    mem_adjointLattice_congr h, mem_centralizerLattice_congr h, mem_endFiltration_congr h]

theorem criticalExponent_congr (β : Module.End K V) :
    criticalExponent 𝓛 β = criticalExponent 𝓛' β := by
  simp only [criticalExponent, criticalIndexSet_congr h]

theorem valuation_congr (x : Module.End K V) : 𝓛.valuation x = 𝓛'.valuation x := by
  simp only [valuation, mem_endFiltration_congr h]

theorem mem_stabilizer_congr {g : (Module.End K V)ˣ} :
    g ∈ 𝓛.stabilizer ↔ g ∈ 𝓛'.stabilizer := by
  simp only [mem_stabilizer, ← SetLike.coe_set_eq, Submodule.map_coe, h,
    LinearMap.coe_restrictScalars]

end LatticeChain

end Congr

section Transfer

variable {O : Type uO} {O' : Type uO'} {K : Type uK} {V : Type uV} [CommRing O] [CommRing O']
  [Field K] [Algebra O K] [Algebra O' K] [AddCommGroup V] [Module K V]
  [Module O V] [IsScalarTower O K V] [Module O' V] [IsScalarTower O' K V]

private theorem mem_jacobson_map (φ : O ≃+* O') {a : O} :
    φ a ∈ Ring.jacobson O' ↔ a ∈ Ring.jacobson O := by
  rw [← Ideal.jacobson_bot, ← Ideal.jacobson_bot, Ideal.mem_jacobson_bot,
    Ideal.mem_jacobson_bot]
  constructor
  · intro ha y
    have := ha (φ y)
    rwa [← map_mul, ← map_one φ, ← map_add, MulEquiv.isUnit_map φ] at this
  · intro ha y
    have := ha (φ.symm y)
    rwa [← MulEquiv.isUnit_map φ, map_add, map_mul, map_one, RingEquiv.apply_symm_apply] at this

namespace LatticeChain

variable (𝓛 : LatticeChain O K V) (φ : O ≃+* O')
  (hφ : ∀ a, algebraMap O' K (φ a) = algebraMap O K a)

include hφ in
private theorem smul_eq_transfer (a : O) (v : V) : φ a • v = a • v := by
  rw [← algebraMap_smul K (φ a) v, hφ, algebraMap_smul]

/-- The lattice `L_i` viewed as a module over the second integer ring. -/
def transferLattice (i : ℤ) : Submodule O' V where
  carrier := 𝓛.lattice i
  add_mem' := (𝓛.lattice i).add_mem
  zero_mem' := (𝓛.lattice i).zero_mem
  smul_mem' a v hv := by
    change a • v ∈ 𝓛.lattice i
    rw [← RingEquiv.apply_symm_apply φ a, smul_eq_transfer φ hφ]
    exact (𝓛.lattice i).smul_mem _ hv

theorem coe_transferLattice (i : ℤ) :
    (𝓛.transferLattice φ hφ i : Set V) = 𝓛.lattice i := rfl

private theorem transferLattice_fg (i : ℤ) : (𝓛.transferLattice φ hφ i).FG := by
  obtain ⟨s, hs⟩ := (𝓛.isLattice i).fg
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro v hv
    change v ∈ 𝓛.lattice i
    rw [← hs]
    exact Submodule.subset_span hv
  · intro v hv
    change v ∈ 𝓛.lattice i at hv
    rw [← hs] at hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx =>
      rw [← smul_eq_transfer φ hφ]
      exact Submodule.smul_mem _ _ hx

private theorem transferLattice_smul (J : Ideal O) (J' : Ideal O')
    (hJ : ∀ a, φ a ∈ J' ↔ a ∈ J) (i j : ℤ) (hij : 𝓛.lattice j = J • 𝓛.lattice i) :
    𝓛.transferLattice φ hφ j = J' • 𝓛.transferLattice φ hφ i := by
  apply le_antisymm
  · intro v hv
    change v ∈ 𝓛.lattice j at hv
    rw [hij] at hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha w hw
      rw [← smul_eq_transfer φ hφ]
      exact Submodule.smul_mem_smul ((hJ a).mpr ha) hw
    · intro x y hx hy
      exact add_mem hx hy
  · intro v hv
    change v ∈ 𝓛.lattice j
    rw [hij]
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha w hw
      rw [← RingEquiv.apply_symm_apply φ a, smul_eq_transfer φ hφ]
      refine Submodule.smul_mem_smul ((hJ _).mp ?_) hw
      rwa [RingEquiv.apply_symm_apply]
    · intro x y hx hy
      exact add_mem hx hy

/-- The same lattice chain viewed over a second integer ring with the same image in `K`. -/
def transfer : LatticeChain O' K V where
  lattice := 𝓛.transferLattice φ hφ
  isLattice i := ⟨𝓛.transferLattice_fg φ hφ i, (𝓛.isLattice i).span_eq_top⟩
  lattice_succ_lt i := by
    rw [← SetLike.coe_ssubset_coe, coe_transferLattice, coe_transferLattice,
      SetLike.coe_ssubset_coe]
    exact 𝓛.lattice_succ_lt i
  exists_period := by
    obtain ⟨e, he, hper⟩ := 𝓛.exists_period
    exact ⟨e, he, fun i => 𝓛.transferLattice_smul φ hφ _ _
      (fun a => mem_jacobson_map φ) i (i + e) (hper i)⟩

theorem transfer_lattice (i : ℤ) :
    ((𝓛.transfer φ hφ).lattice i : Set V) = 𝓛.lattice i := rfl

end LatticeChain

end Transfer

end Langlands.BushnellKutzko
