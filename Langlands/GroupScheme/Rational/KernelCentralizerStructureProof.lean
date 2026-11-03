import Langlands.GroupScheme.FieldFixedSubgroupRepresentabilityProof
import Langlands.GroupScheme.Rational.KernelCentralizerTangent
import Langlands.GroupScheme.Rational.KernelCentralizerClosed
import Langlands.GroupScheme.Rational.KernelCentralizerSmooth
import Langlands.GroupScheme.Rational.KernelWeightImage
import Langlands.GroupScheme.Torus.DiagonalizableFixedSmoothProof

/-! # Smooth character-kernel centralizers and their integral Lie image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The exact kernel-centralizer structure target, with all integral weights. -/
theorem kernelCentralizerStructure : KernelCentralizerStructureStatement.{u} := by
  intro k _ G hG hAff S hS i a _ha
  let : IsAffineHom G.X.hom := hAff
  let : Smooth G.X.hom := hG
  let : IsAffineHom S.X.hom := hS.isAffineHom
  let : AddGroup.FG (Diagonalizable.quotientLattice a) :=
    Diagonalizable.quotientLattice_fg S hS a
  have hSpan : kernelLieInvariants i a = integralWeightSpan i a :=
    le_antisymm (kernelLieInvariants_le_integralWeightSpan G S hS i a)
      (integralWeightSpan_le_kernelLieInvariants i a)
  obtain ⟨C, j, hj, hclosed⟩ :=
    kernelCentralizer_isClosedRepresentable_of_fieldFixed
      fieldFixedSubgroupRepresentability i a
  refine ⟨C, j, hj, hclosed, ?_, ?_⟩
  · exact kernelCentralizer_smooth_of_diagonalizableIso
      Diagonalizable.FixedSmooth.fixedSubgroupSmooth i a
      (Diagonalizable.kernelDiagonalizableIso S hS a) hG inferInstance j hj hclosed
  · rw [← hSpan]
    exact kernelCentralizer_hasLieImage i a

end Langlands.GroupScheme.RelativeRoot
