import Langlands.BushnellKutzko.AdjointExactnessProof
import Langlands.BushnellKutzko.LatticeChainShifts

/-! # Reduction of critical-exponent equality to the next adjoint lattice -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uO uF uV uE

private theorem adjointLattice_eq_endFiltration_zero_of_stabilizer
    {O : Type uO} {F : Type uF} {V : Type uV} [CommRing O] [Field F]
    [Algebra O F] [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]
    (L : LatticeChain O F V) (g : L.stabilizer) :
    adjointLattice L (g.val : Module.End F V) (L.stabilizerValuation g) =
      L.endFiltration 0 := by
  let b : Module.End F V := g.val
  let d := L.stabilizerValuation g
  have hb : b ∈ L.endFiltration d := by
    intro i v hv
    have hmap := Submodule.mem_map_of_mem (f := b.restrictScalars O) hv
    rwa [L.map_lattice_stabilizer g] at hmap
  refine le_antisymm inf_le_left fun x hx => ⟨hx, ?_⟩
  change b * x - x * b ∈ L.endFiltration d
  exact sub_mem
    (by simpa only [add_zero] using L.mul_mem_endFiltration hb hx)
    (by simpa only [zero_add] using L.mul_mem_endFiltration hx hb)

/-- The critical maximum bounds the order valuation. Equality occurs exactly when the adjoint
lattice one step above the shift lies in the centralizer lattice plus the radical. -/
theorem criticalExponent_ge_shift_and_eq_iff
    {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {V : Type uV} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (L : LatticeChain 𝒪[F] F V)
    (hnormal : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    (u : Eˣ) (hgen : Algebra.adjoin F ({(u : E)} : Set E) = ⊤)
    (hnscalar : ¬ ∃ a : F, algebraMap F E a = (u : E)) :
    let b := subfieldEmbedding F E V (u : E)
    let d := (L.fieldShift E hnormal u).toAdd
    ∃ k₀ : ℤ, criticalExponent L b = (k₀ : WithBot ℤ) ∧
      L.valuation b ≤ (k₀ : WithTop ℤ) ∧
      (L.valuation b = (k₀ : WithTop ℤ) ↔
        adjointLattice L b (d + 1) ≤ centralizerLattice L b 0 ⊔ L.endFiltration 1) := by
  dsimp only
  let b := subfieldEmbedding F E V (u : E)
  let g : L.stabilizer := ⟨subfieldUnits F E V u, hnormal u⟩
  let d := L.stabilizerValuation g
  obtain ⟨_, ⟨j, hj⟩, _, ⟨k₀, hk₀, hcrit⟩, _⟩ :=
    adjointExactness F V E L (u : E) hgen hnscalar hnormal
  have hd : d ∈ criticalIndexSet L b := by
    intro h
    have hadj : adjointLattice L b d = L.endFiltration 0 :=
      adjointLattice_eq_endFiltration_zero_of_stabilizer L g
    rw [hadj] at h
    exact hj (inf_le_left.trans h)
  have hd_le : d ≤ k₀ := hk₀.2 hd
  have hv : L.valuation b = (d : WithTop ℤ) := L.valuation_eq_shift g
  rw [hv]
  refine ⟨k₀, hcrit, WithTop.coe_le_coe.mpr hd_le, ?_⟩
  rw [WithTop.coe_eq_coe]
  change d = k₀ ↔ adjointLattice L b (d + 1) ≤ centralizerLattice L b 0 ⊔ L.endFiltration 1
  constructor
  · rintro rfl
    by_contra h
    have hnext := hk₀.2 (show d + 1 ∈ criticalIndexSet L b from h)
    omega
  · intro h
    apply le_antisymm hd_le
    by_contra! hlt
    have hnext : d + 1 ≤ k₀ := by omega
    exact hk₀.1 ((adjointLattice_antitone L b hnext).trans h)

end Langlands.BushnellKutzko
