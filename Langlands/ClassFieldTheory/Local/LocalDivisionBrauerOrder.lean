import Langlands.ClassFieldTheory.Local.BrauerLocalInvariant
import Langlands.ClassFieldTheory.Local.LocalDivisionSplittingDegree

noncomputable section

open Langlands.Brauer Langlands.CentralDivision Langlands.LocalField ValuativeRel

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A finite base extension kills exactly the Brauer classes annihilated by its degree. -/
theorem scalarExtension_eq_zero_iff_degree_nsmul (L : Type u) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [FiniteDimensional K L] (hcont : Continuous (algebraMap K L)) (x : BrauerGroup.{u, u} K) :
    scalarExtension L x = 0 ↔ Module.finrank K L • x = 0 := by
  calc
    scalarExtension L x = 0 ↔ localBrauerInvariant L (scalarExtension L x) = localBrauerInvariant L 0 :=
      (localBrauerInvariant L).injective.eq_iff.symm
    _ ↔ localBrauerInvariant K (Module.finrank K L • x) = localBrauerInvariant K 0 := by
      rw [localBrauerInvariant_scalarExtension K L hcont, map_nsmul, map_zero, map_zero]
    _ ↔ Module.finrank K L • x = 0 := (localBrauerInvariant K).injective.eq_iff

variable (D : Type u) [DivisionRing D] [Algebra K D] [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The exact order of the class of a local central division algebra is its degree. -/
theorem addOrderOf_localDivisionClass {n : ℕ} (hd : Module.finrank K D = n * n) :
    addOrderOf (classOf (divisionAlgebraCSA K D)) = n := by
  let x := classOf (divisionAlgebraCSA K D)
  let d := addOrderOf x
  have hdvd : d ∣ n := by
    obtain ⟨E, hfield, hAlg, hfinite, hdeg, hsplit⟩ := exists_localDivision_splittingDegree K D hd
    let := hfield
    let := hAlg
    let := hfinite
    let := FiniteExtension.normedField K E
    let := FiniteExtension.valuativeRel K E
    let := FiniteExtension.isLocalField K E
    let := spectralFiniteExtension_valuativeExtension K E
    have h := (scalarExtension_eq_zero_iff_degree_nsmul K E
      (spectralFiniteExtension_algebraMap_continuous K E) x).1 hsplit
    rw [hdeg] at h
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
  have hn : 0 < n := by
    have h := Module.finrank_pos (R := K) (M := D)
    rw [hd] at h
    exact Nat.pos_of_mul_pos_left h
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  let E := finiteUnramifiedFieldOfDegree K d hdpos
  let : FiniteDimensional K E := finiteUnramifiedFieldOfDegree_finiteDimensional K d hdpos
  let := FiniteExtension.normedField K E
  let := FiniteExtension.valuativeRel K E
  let := FiniteExtension.isLocalField K E
  let := spectralFiniteExtension_valuativeExtension K E
  have hdeg : Module.finrank K E = d := finiteUnramifiedFieldOfDegree_finrank K d hdpos
  have hsplit : scalarExtension E x = 0 := by
    apply (scalarExtension_eq_zero_iff_degree_nsmul K E
      (spectralFiniteExtension_algebraMap_continuous K E) x).2
    rw [hdeg]
    exact addOrderOf_nsmul_eq_zero x
  have hndvd := divisionDegree_dvd_of_scalarExtension_eq_zero K D E hd hsplit
  rw [hdeg] at hndvd
  exact Nat.dvd_antisymm hdvd hndvd

private theorem denominatorEquiv_two_one :
    (denominatorEquiv 2 (by decide) 1 : RationalModIntegers) = rationalClass (1 / 2 : ℚ) := by
  rw [denominatorEquiv_one]
  simp [reciprocalClass, one_div]

/-- The invariant of a central division algebra of degree two is the actual rational half. -/
theorem localBrauerInvariant_division_degree_two (hd : Module.finrank K D = 2 * 2) :
    localBrauerInvariant K (classOf (divisionAlgebraCSA K D)) = rationalClass (1 / 2 : ℚ) := by
  let a := classOf (divisionAlgebraCSA K D)
  let q := localBrauerInvariant K a
  have ha : 2 • a = 0 := by
    rw [← addOrderOf_localDivisionClass K D hd]
    exact addOrderOf_nsmul_eq_zero a
  have hq : q ∈ denominatorSubgroup 2 := by
    change 2 • localBrauerInvariant K a = 0
    rw [← map_nsmul, ha, map_zero]
  have hq0 : q ≠ 0 := by
    intro h
    exact divisionBrauerClass_ne_zero_of_degree_two K D hd
      ((localBrauerInvariant K).injective (h.trans (map_zero _).symm))
  let e := denominatorEquiv 2 (by decide)
  obtain ⟨t, ht⟩ := e.surjective ⟨q, hq⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hq0 ((congrArg Subtype.val ht).symm.trans (by rw [map_zero]; rfl))
  have ht1 : t = 1 := by
    have hv := ZMod.val_lt t
    have h : t.val = 0 ∨ t.val = 1 := by omega
    rcases h with h | h
    · exact (ht0 (ZMod.val_injective 2 (h.trans ZMod.val_zero.symm))).elim
    · exact ZMod.val_injective 2 (h.trans (ZMod.val_one'' (by decide)).symm)
  exact (congrArg Subtype.val ht).symm.trans (by rw [ht1]; exact denominatorEquiv_two_one)

end Langlands.ClassFieldTheory.Local
