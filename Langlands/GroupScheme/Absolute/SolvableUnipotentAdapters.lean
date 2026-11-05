import Langlands.GroupScheme.Absolute.TriangularCoordinateCharacters
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitTorus
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Adapters for the triangular-kernel construction of the unipotent part -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The diagonal group for the descending weights is a split torus. -/
theorem isSplitTorus_triangularLevi (N : ℕ) (R : CommRingCat.{u}) :
    IsSplitTorus
      (GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ))) := by
  exact ⟨ULift.{u} (Fin N), inferInstance,
    ⟨(GeneralLinear.diagonalTorusIso _ (TriangularLayer.triangularWeights_injective (N := N)) R).symm⟩⟩

namespace GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) (e : n → ℤ)

/-- A concrete block unitriangular group is affine over its base. -/
theorem isAffineHom_blockUnipotentScheme :
    IsAffineHom (blockUnipotentScheme n R e).X.hom := by
  let : IsClosedImmersion (blockUnipotentHom n R e).hom.hom.left :=
    isClosedSubgroup_blockUnipotentHom n R e
  have h : IsAffineHom
      ((blockUnipotentHom n R e).hom.hom.left ≫ (groupScheme n R).X.hom) :=
    inferInstance
  simpa only [Over.w] using h

/-- A concrete block unitriangular group is locally of finite type over its base. -/
theorem locallyOfFiniteType_blockUnipotentScheme :
    LocallyOfFiniteType (blockUnipotentScheme n R e).X.hom := by
  let : Smooth (groupScheme n R).X.hom := smoothStatement n R
  let : IsClosedImmersion (blockUnipotentHom n R e).hom.hom.left :=
    isClosedSubgroup_blockUnipotentHom n R e
  have h : LocallyOfFiniteType
      ((blockUnipotentHom n R e).hom.hom.left ≫ (groupScheme n R).X.hom) :=
    inferInstance
  simpa only [Over.w] using h

end GeneralLinear

end Langlands.GroupScheme
