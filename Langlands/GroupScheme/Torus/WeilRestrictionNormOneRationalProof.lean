import Langlands.GroupScheme.Torus.WeilRestrictionNormOneRationalStatements
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneFixedProof
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Ground-field norm-one lattice vanishing -/

noncomputable section

universe u

namespace Langlands.GroupScheme.WeilGm

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K]

/-- Canonical base change embeds the ground-field norm-one lattices into
the zero fixed lattices over an algebraic closure. -/
theorem normOneRationalLattices : normOneRationalLatticesStatement k K := by
  intro hsep
  have hfixed := normOneGaloisFixedLattices k K (AlgebraicClosure k) hsep
    inferInstance (fun _ => IsAlgClosed.splits _)
  constructor
  · intro χ
    apply characterLattice.algebraBaseChange_injective k (AlgebraicClosure k)
      (normOneCommGroupScheme (CommRingCat.of k) K)
    rw [map_zero]
    apply (hfixed.2.2.2.2 _).mp
    intro σ
    exact characterLattice.galoisRepresentation_baseChange k (AlgebraicClosure k)
      (normOneCommGroupScheme (CommRingCat.of k) K) σ χ
  · intro ν
    apply cocharacterLattice.algebraBaseChange_injective k (AlgebraicClosure k)
      (normOneCommGroupScheme (CommRingCat.of k) K)
    rw [map_zero]
    apply (hfixed.2.2.2.1 _).mp
    intro σ
    exact cocharacterLattice.galoisRepresentation_baseChange k (AlgebraicClosure k)
      (normOneCommGroupScheme (CommRingCat.of k) K) σ ν

end Langlands.GroupScheme.WeilGm
