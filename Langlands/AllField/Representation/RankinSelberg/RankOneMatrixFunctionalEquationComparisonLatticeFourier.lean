import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonLatticeFourier
import Langlands.AllField.HarmonicAnalysis.PadicLatticeFourierProof
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
/-! Actual rectangular Fourier integrals of entrywise affine lattice boxes. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicScalarHaarScaling rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis

universe uF

section Tensor


end Tensor

section Padic

variable (F : Type uF) [Field F] (T : LocalFieldData F)

variable {r s : ℕ}

/-- The actual entrywise affine lattice box, with independent integer levels. -/
def rectangularLatticeCoset (m : Fin r → Fin s → ℤ)
    (A : Matrix (Fin r) (Fin s) F) :
    Set (Matrix (Fin r) (Fin s) F) :=
  Set.univ.pi fun i => Set.univ.pi fun j =>
    {x | x - A i j ∈ T.additiveLattice (m i j)}

@[simp] theorem mem_rectangularLatticeCoset (m : Fin r → Fin s → ℤ)
    (A X : Matrix (Fin r) (Fin s) F) :
    X ∈ rectangularLatticeCoset F T m A ↔
      ∀ i j, X i j - A i j ∈ T.additiveLattice (m i j) := by
  change (∀ i ∈ Set.univ, ∀ j ∈ Set.univ,
    X i j - A i j ∈ T.additiveLattice (m i j)) ↔ _
  simp only [Set.mem_univ, forall_const]

private theorem coset_compact (m : ℤ) (a : F) :
    letI := T.topology
    IsCompact {x : F | x - a ∈ T.additiveLattice m} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hC : {x : F | x - a ∈ T.additiveLattice m} =
      (fun t => t + a) '' (T.additiveLattice m : Set F) := by
    ext x
    constructor
    · intro hx
      exact ⟨x - a, hx, sub_add_cancel x a⟩
    · rintro ⟨t, ht, rfl⟩
      simpa only [Set.mem_ofPred_eq, add_sub_cancel_right, SetLike.mem_coe] using ht
  rw [hC]
  exact (T.isCompact_additiveLattice m).image (continuous_id.add continuous_const)

/-- Entrywise affine lattice boxes are compact, including empty dimensions. -/
theorem isCompact_rectangularLatticeCoset (m : Fin r → Fin s → ℤ)
    (A : Matrix (Fin r) (Fin s) F) :
    letI := T.topology
    IsCompact (rectangularLatticeCoset F T m A) := by
  let := T.topology
  exact isCompact_univ_pi fun i =>
    isCompact_univ_pi fun j => coset_compact F T (m i j) (A i j)

/-- Entrywise affine lattice boxes are clopen. -/
theorem isClopen_rectangularLatticeCoset (m : Fin r → Fin s → ℤ)
    (A : Matrix (Fin r) (Fin s) F) :
    letI := T.topology
    IsClopen (rectangularLatticeCoset F T m A) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  refine ⟨(isCompact_rectangularLatticeCoset F T m A).isClosed, ?_⟩
  exact isOpen_set_pi Set.finite_univ fun i _ =>
    isOpen_set_pi Set.finite_univ fun j _ =>
      (T.isOpen_additiveLattice (m i j)).preimage (continuous_id.sub continuous_const)

/-- The characteristic function of the actual affine lattice box, as a
Schwartz–Bruhat test on the full rectangular matrix space. -/
def rectangularLatticeCosetTest (m : Fin r → Fin s → ℤ)
    (A : Matrix (Fin r) (Fin s) F) :
    letI := T.topology
    SchwartzBruhat (Matrix (Fin r) (Fin s) F) := by
  letI := T.topology
  exact Hecke.TestFunction.characteristic
    (isClopen_rectangularLatticeCoset F T m A)
    (isCompact_rectangularLatticeCoset F T m A)

@[simp] theorem rectangularLatticeCosetTest_apply (m : Fin r → Fin s → ℤ)
    (A X : Matrix (Fin r) (Fin s) F) :
    letI := T.topology
    rectangularLatticeCosetTest F T m A X =
      (rectangularLatticeCoset F T m A).indicator (fun _ => (1 : ℂ)) X := rfl

end Padic

end Langlands.AllField.HarmonicAnalysis
