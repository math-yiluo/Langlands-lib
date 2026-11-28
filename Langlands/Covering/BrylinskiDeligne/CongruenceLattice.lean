import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-! # The integral lattice cut out by a bilinear congruence -/

namespace Langlands.Covering.BrylinskiDeligne

variable {Y : Type*} [AddCommGroup Y]

/-- The submodule of vectors whose pairing with every vector of `Y` is divisible by `n`.
This is the congruence of Gan–Gao §3.4 and Weissman Construction 1.3, with an arbitrary
integral bilinear form in place of the polarization. -/
def congruenceLattice (B : LinearMap.BilinForm ℤ Y) (n : ℕ) : Submodule ℤ Y where
  carrier := {y | ∀ z : Y, (n : ℤ) ∣ B y z}
  zero_mem' z := by simp
  add_mem' hy hy' z := by
    simpa only [map_add, LinearMap.add_apply] using dvd_add (hy z) (hy' z)
  smul_mem' a y hy z := by
    rw [LinearMap.map_smul₂, smul_eq_mul]
    exact (hy z).trans (dvd_mul_left _ _)

variable (B : LinearMap.BilinForm ℤ Y) (n : ℕ)

@[simp] theorem mem_congruenceLattice {y : Y} :
    y ∈ congruenceLattice B n ↔ ∀ z : Y, (n : ℤ) ∣ B y z :=
  Iff.rfl

/-- The inclusion into the original lattice. -/
abbrev congruenceLatticeInclusion : congruenceLattice B n →ₗ[ℤ] Y :=
  (congruenceLattice B n).subtype

theorem congruenceLatticeInclusion_injective :
    Function.Injective (congruenceLatticeInclusion B n) :=
  (congruenceLattice B n).subtype_injective

/-- The congruence holds for every `n`-fold multiple from the original lattice. -/
theorem smul_mem_congruenceLattice (y : Y) : (n : ℤ) • y ∈ congruenceLattice B n := by
  intro z
  rw [LinearMap.map_smul₂, smul_eq_mul]
  exact dvd_mul_right _ _

theorem range_lsmul_le_congruenceLattice :
    LinearMap.range (LinearMap.lsmul ℤ Y (n : ℤ)) ≤ congruenceLattice B n := by
  rintro _ ⟨y, rfl⟩
  exact smul_mem_congruenceLattice B n y

@[simp] theorem congruenceLattice_one : congruenceLattice B 1 = ⊤ := by
  ext y
  simp

/-- A bilinear-form-preserving equivalence preserves and reflects the congruence. -/
theorem apply_mem_congruenceLattice_iff (e : Y ≃ₗ[ℤ] Y)
    (hB : ∀ y z, B (e y) (e z) = B y z) (y : Y) :
    e y ∈ congruenceLattice B n ↔ y ∈ congruenceLattice B n := by
  simp only [mem_congruenceLattice]
  constructor
  · intro hy z
    simpa only [hB] using hy (e z)
  · intro hy z
    obtain ⟨z, rfl⟩ := e.surjective z
    simpa only [hB] using hy z

/-- The restriction of an equivalence preserving the integral bilinear form. -/
def congruenceLatticeEquiv (e : Y ≃ₗ[ℤ] Y)
    (hB : ∀ y z, B (e y) (e z) = B y z) :
    congruenceLattice B n ≃ₗ[ℤ] congruenceLattice B n :=
  e.ofSubmodules _ _ <| by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (apply_mem_congruenceLattice_iff B n e hB y).2 hy
    · intro hz
      obtain ⟨y, rfl⟩ := e.surjective z
      exact ⟨y, (apply_mem_congruenceLattice_iff B n e hB y).1 hz, rfl⟩

@[simp] theorem congruenceLatticeInclusion_equiv_apply (e : Y ≃ₗ[ℤ] Y)
    (hB : ∀ y z, B (e y) (e z) = B y z) (y : congruenceLattice B n) :
    congruenceLatticeInclusion B n (congruenceLatticeEquiv B n e hB y) =
      e (congruenceLatticeInclusion B n y) :=
  rfl

section FiniteFree

/-- An integral submodule of a finitely generated lattice is finitely generated. -/
theorem congruenceLattice_finite [Module.Finite ℤ Y] : Module.Finite ℤ (congruenceLattice B n) :=
  inferInstance

/-- The congruence submodule of a finite free integral lattice is free. -/
theorem congruenceLattice_free [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    Module.Free ℤ (congruenceLattice B n) :=
  inferInstance

variable [Module.Finite ℤ Y] [Module.Free ℤ Y]

/-- The inclusion has full rank because multiplication by the positive degree factors through it. -/
theorem congruenceLattice_finrank (hn : 0 < n) :
    Module.finrank ℤ (congruenceLattice B n) = Module.finrank ℤ Y := by
  have hn' : (n : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hn.ne'
  let f := (LinearMap.lsmul ℤ Y (n : ℤ)).codRestrict (congruenceLattice B n)
    (smul_mem_congruenceLattice B n)
  have hf : Function.Injective f := (LinearMap.lsmul_injective hn').codRestrict _
  exact le_antisymm (Submodule.finrank_le _) (f.finrank_le_finrank_of_injective hf)

/-- The quotient of the original lattice by the congruence submodule is finite. -/
theorem congruenceLattice_finiteQuotient (hn : 0 < n) : Finite (Y ⧸ congruenceLattice B n) :=
  Submodule.finiteQuotientOfFreeOfRankEq _ (congruenceLattice_finrank B n hn)

end FiniteFree

end Langlands.Covering.BrylinskiDeligne
