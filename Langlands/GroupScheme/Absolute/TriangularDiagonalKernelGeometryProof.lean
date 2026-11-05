import Langlands.GroupScheme.Absolute.TriangularDiagonalKernelGeometryStatement
import Langlands.GroupScheme.Absolute.TriangularDiagonalSplittingAssembly
import Langlands.GroupScheme.SplitKernelRetractGeometry

/-! # Geometry of the actual diagonal kernel of a triangular subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual diagonal kernel of a smooth connected affine triangular subgroup over an
algebraically closed field is smooth and connected. -/
theorem triangularDiagonalKernelGeometry :
    TriangularDiagonalKernelGeometryStatement.{u} := by
  intro k _ _ H _ _ _ N j hj
  obtain ⟨D, d, q, s, hd, hf, hs⟩ := triangularDiagonalSplitting k H N j hj
  have : IsClosedImmersion d.hom.hom.left := hd
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have : IsAffine (GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))).X.left := by
    change IsAffine (Spec _)
    infer_instance
  exact SplitKernelRetract.smooth_connected_kernel
    (j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))) d q s hf hs

end Langlands.GroupScheme
