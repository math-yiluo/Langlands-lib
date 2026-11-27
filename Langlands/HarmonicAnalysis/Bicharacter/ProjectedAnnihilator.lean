import Langlands.HarmonicAnalysis.Bicharacter.CompactOpenDuality

/-! # Dual lattices for an intersection with a subspace -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open Set Filter MeasureTheory
open scoped Pointwise _root_.Topology

/-- For adjoint maps `i` and `p` relative to self-dual bicharacters, the dual of
`i⁻¹(L) ∩ M` is the sum of `p(L*)` and `M*`. -/
def ProjectedAnnihilatorStatement {X Y : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [CompactOpenExhaustion X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] [CompactOpenExhaustion Y] [MeasurableSpace Y] [BorelSpace Y]
    {eX : X → X → ℂ} {eY : Y → Y → ℂ} (hX : IsSelfDualBicharacter eX)
    (hY : IsSelfDualBicharacter eY) (i : Y →+ X) (p : X →+ Y)
    (L : AddSubgroup X) (M : AddSubgroup Y) : Prop :=
  Continuous p → (∀ x y, eY (p x) y = eX x (i y)) →
  IsOpen (L : Set X) → IsCompact (L : Set X) → IsOpen (M : Set Y) → IsCompact (M : Set Y) →
  hY.annihilator ((L.comap i ⊓ M : AddSubgroup Y) : Set Y) =
    (hX.annihilator (L : Set X)).map p ⊔ hY.annihilator (M : Set Y)

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [LocallyCompactSpace X] [SecondCountableTopology X] [CompactOpenExhaustion X]
  [MeasurableSpace X] [BorelSpace X] [AddCommGroup Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
  [CompactOpenExhaustion Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The annihilator of the projected dual sum is the intersection, by adjointness.
Passing to its annihilator again gives the desired sum. -/
theorem projectedAnnihilator {eX : X → X → ℂ} {eY : Y → Y → ℂ}
    (hX : IsSelfDualBicharacter eX) (hY : IsSelfDualBicharacter eY)
    (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure]
    (i : Y →+ X) (p : X →+ Y) (L : AddSubgroup X) (M : AddSubgroup Y) :
    ProjectedAnnihilatorStatement hX hY i p L M := by
  intro hp hcompat hLo hLc hMo hMc
  let A := hX.annihilator (L : Set X)
  let B := hY.annihilator (M : Set Y)
  let P := A.map p ⊔ B
  have hBc : IsCompact (B : Set Y) := hY.isCompact_annihilator_compactOpen M hMo hMc
  have hAc : IsCompact (A : Set X) := hX.isCompact_annihilator_compactOpen L hLo hLc
  have hPA : A.map p ≤ P := le_sup_left
  have hPB : B ≤ P := le_sup_right
  have hPc : IsCompact (P : Set Y) := by
    have hP : (P : Set Y) = (p '' (A : Set X)) + (B : Set Y) := by
      ext y
      change y ∈ A.map p ⊔ B ↔ _
      rw [AddSubgroup.mem_sup, Set.mem_add]
      rfl
    rw [hP]
    exact (hAc.image hp).add hBc
  have hPo : IsOpen (P : Set Y) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    exact Filter.mem_of_superset ((hY.isOpen_annihilator hMc).mem_nhds B.zero_mem) hPB
  have hAL : hX.annihilator (A : Set X) = L := compactOpenDoubleAnnihilator hX L μ hLo hLc
  have hBM : hY.annihilator (B : Set Y) = M := compactOpenDoubleAnnihilator hY M ν hMo hMc
  have hAnn : hY.annihilator (P : Set Y) = L.comap i ⊓ M := by
    ext y
    constructor
    · intro hy
      have hyA : i y ∈ hX.annihilator (A : Set X) := by
        intro x hx
        rw [← hcompat]
        exact hy (p x) (hPA (AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩))
      have hyB : y ∈ hY.annihilator (B : Set Y) := fun z hz => hy z (hPB hz)
      rw [hAL] at hyA
      rw [hBM] at hyB
      exact ⟨hyA, hyB⟩
    · rintro ⟨hyL, hyM⟩ z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hz
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp ha
      have hyA : i y ∈ hX.annihilator (A : Set X) := hAL.symm ▸ hyL
      have hyB : y ∈ hY.annihilator (B : Set Y) := hBM.symm ▸ hyM
      rw [hY.map_add_left, hcompat, hyA x hx, hyB b hb, one_mul]
  change hY.annihilator ((L.comap i ⊓ M : AddSubgroup Y) : Set Y) = P
  rw [← hAnn]
  exact compactOpenDoubleAnnihilator hY P ν hPo hPc

end Langlands.HarmonicAnalysis
