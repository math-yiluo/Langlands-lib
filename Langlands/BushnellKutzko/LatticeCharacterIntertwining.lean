import Langlands.BushnellKutzko.TraceDualLatticeCalculus
import Langlands.BushnellKutzko.CharacterCommutatorDepth
import Langlands.BushnellKutzko.SimpleCharacterCovarianceStatement
import Langlands.BushnellKutzko.LatticeCosetConjugation

/-! # Character intertwining and formal intertwining of the dual lattice coset -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "O" => 𝒪[F]

/-- Formal intertwining is equivalent to the parameter's conjugation
difference lying in the sum of the error lattice and its conjugate. -/
theorem mem_latticeCosetIntertwining_iff_conj_sub_mem_sup (b : A) (D : Submodule O A) (g : G) :
    g ∈ latticeCosetIntertwining b D ↔
      endUnitConjugation g⁻¹ b - b ∈ D ⊔ D.map (endUnitConjugation g⁻¹).toLinearMap := by
  let e := endUnitConjugation g⁻¹
  change (∃ x : A, x - b ∈ D ∧ e x - b ∈ D) ↔ e b - b ∈ D ⊔ D.map e.toLinearMap
  constructor
  · rintro ⟨x, hx, hxg⟩
    have hy : -e (x - b) ∈ D.map e.toLinearMap := neg_mem (Submodule.mem_map_of_mem hx)
    refine Submodule.mem_sup.mpr ⟨_, hxg, _, hy, ?_⟩
    rw [map_sub]
    abel
  · intro h
    obtain ⟨d, hd, eg, heg, he⟩ := Submodule.mem_sup.mp h
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp heg
    refine ⟨b - w, ?_, ?_⟩
    · have hb : b - w - b = -w := by abel
      rw [hb]
      exact neg_mem hw
    · have eq : e (b - w) - b = (e b - b) - e w := by
        rw [map_sub]
        abel
      rw [eq, ← he]
      change d + e w - e w ∈ D
      simpa only [add_sub_cancel_right] using hd

/-- A unit in the overlap of a lattice congruence group and its conjugate
differs from one by an element of the corresponding lattice intersection. -/
theorem mem_congruence_overlap_iff (M : Submodule O A) {H : Subgroup G}
    (hH : ∀ u : G, u ∈ H ↔ (u : A) - 1 ∈ M) (g h : G) :
    (h ∈ H ∧ g * h * g⁻¹ ∈ H) ↔
      (h : A) - 1 ∈ M ⊓ M.map (endUnitConjugation g⁻¹).toLinearMap := by
  rw [hH, hH, Submodule.mem_inf, Submodule.mem_map_equiv, endUnitConjugation_symm, inv_inv]
  have hval : (↑(g * h * g⁻¹) : A) - 1 = endUnitConjugation g ((h : A) - 1) := by
    rw [endUnitConjugation_apply, mul_sub, sub_mul, mul_one, Units.mul_inv]
    rfl
  rw [hval]

/-- On an overlap where the trace-error identity holds, character
intertwining is equivalent to formal intertwining of the dual lattice coset. -/
theorem mem_characterSelfIntertwining_iff_latticeCosetIntertwining
    (L : LatticeChain O F V) (ψF : AddChar F ℂ) (b : A)
    (M D : Submodule O A) {H : Subgroup G} (χ : H →* ℂˣ) (g : G)
    (hH : ∀ u : G, u ∈ H ↔ (u : A) - 1 ∈ M) (hM : M ≤ L.endFiltration 1)
    (hcov : characterConjugationRatio ψF b χ g)
    (hdual : (additiveDual (traceCharacter ψF)
        ((M ⊓ M.map (endUnitConjugation g⁻¹).toLinearMap : Submodule O A) : Set A)) =
      ((D ⊔ D.map (endUnitConjugation g⁻¹).toLinearMap : Submodule O A) : Set A)) :
    g ∈ characterSelfIntertwining χ ↔ g ∈ latticeCosetIntertwining b D := by
  rw [mem_latticeCosetIntertwining_iff_conj_sub_mem_sup]
  change g ∈ characterSelfIntertwining χ ↔ endUnitConjugation g⁻¹ b - b ∈
    ((D ⊔ D.map (endUnitConjugation g⁻¹).toLinearMap : Submodule O A) : Set A)
  rw [← hdual]
  change g ∈ characterSelfIntertwining χ ↔ ∀ y ∈ (M ⊓ M.map (endUnitConjugation g⁻¹).toLinearMap),
    traceCharacter ψF ((endUnitConjugation g⁻¹ b - b) * y) = 1
  constructor
  · intro hg y hy
    obtain ⟨u, _, hu⟩ := L.exists_mem_unitFiltration (n := 1) (by decide) (hM hy.1)
    have hu' : (u : A) - 1 = y := by rw [hu, add_sub_cancel_left]
    have hov := (mem_congruence_overlap_iff M hH g u).mpr (hu'.symm ▸ hy)
    let x : H := ⟨u, hov.1⟩
    have hval := hcov x hov.2
    have heq := hg x hov.2
    rw [heq] at hval
    have hψ := mul_left_cancel₀ (Units.ne_zero (χ x)) (hval.symm.trans (mul_one _).symm)
    change elementCharacter (traceCharacter ψF) ((↑g⁻¹ : A) * b * (g : A) - b) u = 1 at hψ
    simpa only [elementCharacter_apply, hu', endUnitConjugation_apply, inv_inv] using hψ
  · intro htr x hx
    have hm := (mem_congruence_overlap_iff M hH g x).mp ⟨x.property, hx⟩
    have hψ := htr _ hm
    have hval := hcov x hx
    apply Units.ext
    simp only [endUnitConjugation_apply, inv_inv] at hψ
    rw [elementCharacter_apply, hψ, mul_one] at hval
    exact hval

end Langlands.BushnellKutzko
