import Langlands.GroupScheme.Absolute.SolvableUnipotentPartStatement
import Langlands.GroupScheme.Absolute.SolvableUnipotentAdapters
import Langlands.GroupScheme.Absolute.SolvableUnipotentKernelAssembly
import Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingProof
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Absolute.TriangularDiagonalKernelGeometryProof

/-! # The unipotent part of a smooth connected solvable group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected solvable affine group over an algebraically closed field has
a smooth connected normal unipotent closed subgroup containing every unipotent closed subgroup. -/
theorem solvableUnipotentPart :
    SolvableUnipotentPartStatement.{u} := by
  intro k _ _ H _ _ _ hH
  obtain ⟨N, j, hj⟩ := solvableTriangularEmbeddingStatement k H hH
  obtain ⟨hs, hc⟩ := triangularDiagonalKernelGeometry k H N j hj
  let weights : Fin N → ℤ := fun i => -(i.val : ℤ)
  let q := GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) weights
  have hT := isSplitTorus_triangularLevi N (CommRingCat.of k)
  have : IsAffineHom
      (GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k) weights).X.hom :=
    hT.isAffineHom
  have : IsAffineHom
      (GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k) weights).X.hom :=
    GeneralLinear.isAffineHom_blockUnipotentScheme _ _ _
  have : LocallyOfFiniteType
      (GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k) weights).X.hom :=
    GeneralLinear.locallyOfFiniteType_blockUnipotentScheme _ _ _
  have hu : IsUnipotent (kernel (j ≫ q)) :=
    isUnipotent_kernel_comp_of_closedSubgroup unipotentClosedSubgroup j q
      (GeneralLinear.blockUnipotentIsoKernel (Fin N) (CommRingCat.of k) weights)
      hj (unitriangularUnipotent k N)
  exact exists_unipotent_part_of_split_torus_kernel (j ≫ q) hT hs hc hu

end Langlands.GroupScheme
