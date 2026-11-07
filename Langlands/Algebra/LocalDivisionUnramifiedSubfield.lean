import Langlands.Algebra.LocalDivisionResidueLift
import Mathlib.RingTheory.Adjoin.PowerBasis

/-! An original full-residue subfield with the exact residue extension degree. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : Field (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D
local instance : Algebra 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueAlgebra K D

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra.IsCentral K D] in
/-- The original generator, regarded inside its own singleton adjoin, generates that field. -/
theorem residueGenerator_adjoin_eq_top (a : D) :
    letI := residueGeneratorField K D a
    Algebra.adjoin K ({⟨a, residueGenerator_mem K D a⟩} :
      Set (residueGeneratorSubalgebra K D a)) = ⊤ := by
  let := residueGeneratorField K D a
  let E := residueGeneratorSubalgebra K D a
  let c : E := ⟨a, residueGenerator_mem K D a⟩
  have hs : ((↑) : E → D) ⁻¹' ({a} : Set D) = {c} := by
    ext x
    change (x : D) = a ↔ x = c
    constructor
    · exact fun h => Subtype.ext h
    · exact fun h => congrArg Subtype.val h
  rw [← hs]
  exact Algebra.adjoin_adjoin_coe_preimage

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra.IsCentral K D] in
/-- The actual power basis of the original singleton adjoin. -/
def residueGeneratorPowerBasis (a : D) :
    letI := residueGeneratorField K D a
    PowerBasis K (residueGeneratorSubalgebra K D a) := by
  let := residueGeneratorField K D a
  exact PowerBasis.ofAdjoinEqTop
    (Algebra.IsIntegral.isIntegral (⟨a, residueGenerator_mem K D a⟩ :
      residueGeneratorSubalgebra K D a)) (residueGenerator_adjoin_eq_top K D a)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra.IsCentral K D] in
@[simp]
theorem residueGeneratorPowerBasis_gen (a : D) :
    letI := residueGeneratorField K D a
    (residueGeneratorPowerBasis K D a).gen = ⟨a, residueGenerator_mem K D a⟩ := rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra.IsCentral K D] in
/-- The original singleton adjoin has degree equal to the original minimal-polynomial degree. -/
theorem residueGeneratorSubalgebra_finrank (a : D) :
    letI := residueGeneratorField K D a
    Module.finrank K (residueGeneratorSubalgebra K D a) = (minpoly K a).natDegree := by
  let := residueGeneratorField K D a
  let c : residueGeneratorSubalgebra K D a := ⟨a, residueGenerator_mem K D a⟩
  calc
    Module.finrank K (residueGeneratorSubalgebra K D a) = (minpoly K c).natDegree :=
      (residueGeneratorPowerBasis K D a).finrank
    _ = (minpoly K a).natDegree := by
      rw [← minpoly.algHom_eq (residueGeneratorSubalgebra K D a).val
        Subtype.val_injective c]
      rfl

/-- A multiplicative generator of the actual residue generates it as a base-residue algebra. -/
theorem localDivisionResidue_adjoin_eq_top
    (z : DivisionValuation.Residue (localReducedNormValuation K D))
    (hgen : ∀ y : DivisionValuation.Residue (localReducedNormValuation K D),
      y = 0 ∨ ∃ n : ℕ, y = z ^ n) :
    Algebra.adjoin 𝓀[K] {z} = ⊤ := by
  apply top_unique
  intro y _
  rcases hgen y with rfl | ⟨n, rfl⟩
  · exact (Algebra.adjoin 𝓀[K] {z}).zero_mem
  · exact (Algebra.adjoin 𝓀[K] {z}).pow_mem (Algebra.self_mem_adjoin_singleton _ _) n

/-- A monic polynomial and its original integral root produce a full-residue field of exact degree. -/
theorem exists_localDivision_fullResidue_polynomial_subfield :
    ∃ f : Polynomial 𝒪[K], ∃ b : (localReducedNormValuation K D).integer,
      letI := residueGeneratorField K D (b : D)
      f.Monic ∧
        f.map (IsLocalRing.residue 𝒪[K]) =
          minpoly 𝓀[K] (DivisionValuation.reduction _ b) ∧
        f.map (algebraMap 𝒪[K] K) = minpoly K (b : D) ∧
        IsSeparable K (b : D) ∧
        Function.Surjective (localDivisionSubfieldResidueMap K D
          (residueGeneratorSubalgebra K D (b : D)).val) ∧
        Module.finrank K (residueGeneratorSubalgebra K D (b : D)) =
          Module.finrank 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) := by
  let v := localReducedNormValuation K D
  let R := DivisionValuation.Residue v
  obtain ⟨a, ha⟩ := exists_localDivisionResidue_generator K D
  let z : R := DivisionValuation.reduction v a.val
  have hgen : ∀ y : R, y = 0 ∨ ∃ n : ℕ, y = z ^ n := by
    intro y
    rcases ha y with hy | ⟨n, hn⟩
    · exact Or.inl hy
    · exact Or.inr ⟨n, hn.trans (map_pow _ _ _)⟩
  have hz : z ≠ 0 := isUnit_iff_ne_zero.mp (a.isUnit.map (DivisionValuation.reduction v))
  obtain ⟨f, b, hmon, hmap, hdeg, hmin, hb, hsep⟩ :=
    exists_localDivision_residue_minpoly_lift K D z
  have hbu : IsUnit b := by
    apply (DivisionValuation.isUnit_iff_value_eq_one v b).mpr
    refine le_antisymm b.prop (not_lt.mp ?_)
    intro h
    exact hz (hb ▸ (DivisionValuation.reduction_eq_zero_iff v b).mpr h)
  obtain ⟨bunit, hbunit⟩ := hbu
  refine ⟨f, b, ?_⟩
  let := residueGeneratorField K D (b : D)
  refine ⟨hmon, by rw [hb]; exact hmap, hmin, hsep, ?_, ?_⟩
  · apply localDivisionSubfieldResidueMap_surjective K D _ bunit
    · refine ⟨⟨b, residueGenerator_mem K D (b : D)⟩, ?_⟩
      exact congrArg Subtype.val hbunit.symm
    · intro y
      rcases hgen y with hy | ⟨n, hn⟩
      · exact Or.inl hy
      · refine Or.inr ⟨n, ?_⟩
        rw [map_pow, hbunit, hb]
        exact hn
  · rw [residueGeneratorSubalgebra_finrank, ← hmin, hmon.natDegree_map, hdeg]
    exact (PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral z)
      (localDivisionResidue_adjoin_eq_top K D z hgen)).finrank.symm

/-- An original separable integral generator yields full residue and exactly its residue degree. -/
theorem exists_localDivision_fullResidue_degree_subfield :
    ∃ b : (localReducedNormValuation K D).integer,
      letI := residueGeneratorField K D (b : D)
      IsSeparable K (b : D) ∧
        Function.Surjective (localDivisionSubfieldResidueMap K D
          (residueGeneratorSubalgebra K D (b : D)).val) ∧
        Module.finrank K (residueGeneratorSubalgebra K D (b : D)) =
          Module.finrank 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) := by
  obtain ⟨f, b, _, _, _, hsep, hsurj, hdim⟩ :=
    exists_localDivision_fullResidue_polynomial_subfield K D
  exact ⟨b, hsep, hsurj, hdim⟩

end Langlands.CentralDivision
