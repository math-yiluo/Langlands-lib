import Langlands.BushnellKutzko.SimpleCharacterCommutatorAlgebra

/-! # The outer subgroup in simple-character intertwining -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private theorem mixedAdjointLattice_le_adjointLattice (L : LatticeChain O F V) (b : A)
    {k j : ℤ} (hk : 0 ≤ k) : mixedAdjointLattice L b k j ≤ adjointLattice L b j :=
  fun _ h => ⟨L.endFiltration_antitone hk h.1, L.endFiltration_antitone (by omega) h.2⟩

private theorem unit_mem_adjointLattice_of_mixed (L : LatticeChain O F V) (b : A)
    {k : ℕ} {j : ℤ} {hk : 1 ≤ k} {x : G} (hx : x ∈ mixedAdjointUnitGroup L b k j hk) :
    (x : A) ∈ adjointLattice L b j := by
  have h1 : (1 : A) ∈ adjointLattice L b j := by
    refine ⟨one_mem L.order, ?_⟩
    change b * 1 - 1 * b ∈ L.endFiltration j
    simp
  have h := mixedAdjointLattice_le_adjointLattice L b (Int.natCast_nonneg k)
    (mem_mixedAdjointUnitGroup_iff.mp hx)
  simpa only [sub_add_cancel] using add_mem h h1

/-- A mixed adjoint congruence group normalizes a unit congruence group
if its lattice is stable under left and right multiplication by the adjoint
lattice. -/
theorem mixedAdjointUnitGroup_le_normalizer_of_adjoint_bimodule (L : LatticeChain O F V)
    (b : A) {k : ℕ} (hk : 1 ≤ k) (j : ℤ) (M : Submodule O A) (H : Subgroup G)
    (hH : ∀ g : G, g ∈ H ↔ (g : A) - 1 ∈ M)
    (hNM : adjointLattice L b j * M ≤ M) (hMN : M * adjointLattice L b j ≤ M) :
    mixedAdjointUnitGroup L b k j hk ≤ Subgroup.normalizer (H : Set G) := by
  let X := mixedAdjointUnitGroup L b k j hk
  have hc (x : G) (hx : x ∈ X) (g : G) (hg : g ∈ H) : x * g * x⁻¹ ∈ H := by
    have hxA := unit_mem_adjointLattice_of_mixed L b hx
    have hxiA := unit_mem_adjointLattice_of_mixed L b (X.inv_mem hx)
    apply (hH _).mpr
    have he : (↑(x * g * x⁻¹) : A) - 1 = (x : A) * ((g : A) - 1) * (↑x⁻¹ : A) := by
      simp only [Units.val_mul, mul_sub, mul_one, sub_mul, Units.mul_inv]
    rw [he]
    exact hMN (Submodule.mul_mem_mul (hNM (Submodule.mul_mem_mul hxA ((hH _).mp hg))) hxiA)
  intro x hx
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨hc x hx g, ?_⟩
  intro hg
  have h := hc x⁻¹ (X.inv_mem hx) (x * g * x⁻¹) hg
  convert h using 1
  group

/-- The sum of the mixed lattice and an adjoint-stable congruence lattice
is represented by the product of their unit groups. The product is a subgroup. -/
theorem mixedAdjointUnitGroup_sup_eq_lattice (L : LatticeChain O F V)
    (b : A) {k : ℕ} (hk : 1 ≤ k) (j : ℤ) (M : Submodule O A) (H : Subgroup G)
    (hH : ∀ g : G, g ∈ H ↔ (g : A) - 1 ∈ M)
    (hNM : adjointLattice L b j * M ≤ M) (hMN : M * adjointLattice L b j ≤ M) :
    ((mixedAdjointUnitGroup L b k j hk ⊔ H : Subgroup G) : Set G) =
      {g : G | (g : A) - 1 ∈ mixedAdjointLattice L b k j ⊔ M} := by
  let X := mixedAdjointUnitGroup L b k j hk
  have hN := mixedAdjointUnitGroup_le_normalizer_of_adjoint_bimodule L b hk j M H hH hNM hMN
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X H hN]
  ext g
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    have hxa := mem_mixedAdjointUnitGroup_iff.mp hx
    have hya := (hH _).mp hy
    have he : (↑(x * y) : A) - 1 = ((x : A) - 1) + ((y : A) - 1) + ((x : A) - 1) * ((y : A) - 1) := by
      rw [Units.val_mul]
      noncomm_ring
    have hprod : ((x : A) - 1) * ((y : A) - 1) ∈ M :=
      hNM (Submodule.mul_mem_mul (mixedAdjointLattice_le_adjointLattice L b (Int.natCast_nonneg k) hxa) hya)
    change (↑(x * y) : A) - 1 ∈ mixedAdjointLattice L b k j ⊔ M
    rw [he, add_assoc]
    exact Submodule.add_mem_sup hxa (add_mem hya hprod)
  · intro hg
    have hPos : mixedAdjointLattice L b k j ≤ L.endFiltration 1 := fun _ h =>
      L.endFiltration_antitone (by exact_mod_cast hk) h.1
    have hMul : mixedAdjointLattice L b k j * M ≤ M :=
      (mul_le_mul_left (mixedAdjointLattice_le_adjointLattice L b (Int.natCast_nonneg k)) M).trans hNM
    have hInv (x : G) (hx : (x : A) - 1 ∈ mixedAdjointLattice L b k j) :
        (↑x⁻¹ : A) - 1 ∈ mixedAdjointLattice L b k j := X.inv_mem hx
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_sub_one_mem_sup L hPos hMul hInv hg
    exact ⟨x, hx, y, (hH _).mpr hy, hxy⟩

end Langlands.BushnellKutzko
