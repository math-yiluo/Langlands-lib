import Langlands.GroupScheme.Torus.WeilRestrictionNormOneAnisotropyStatement
import Langlands.GroupScheme.Torus.CocharacterAnisotropy
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneFixedProof
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Anisotropy of the actual finite-separable norm-one torus -/

noncomputable section

universe u

namespace Langlands.GroupScheme.WeilGm

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K]

/-- Every finite separable field extension has an anisotropic actual
norm-one torus, in the split-rank-zero convention. -/
theorem normOneAnisotropy : normOneAnisotropyStatement k K := by
  intro hsep
  apply isAnisotropic_of_cocharacter_eq_zero
    (normOneCommGroupScheme (CommRingCat.of k) K)
  intro ν
  have hfixed := normOneGaloisFixedLattices k K (AlgebraicClosure k) hsep
    inferInstance (fun _ => IsAlgClosed.splits _)
  apply cocharacterLattice.algebraBaseChange_injective k (AlgebraicClosure k)
    (normOneCommGroupScheme (CommRingCat.of k) K)
  rw [map_zero]
  apply (hfixed.2.2.2.1 _).mp
  intro σ
  exact cocharacterLattice.galoisRepresentation_baseChange k (AlgebraicClosure k)
    (normOneCommGroupScheme (CommRingCat.of k) K) σ ν

end Langlands.GroupScheme.WeilGm
