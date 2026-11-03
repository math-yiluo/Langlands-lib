import Langlands.GroupScheme.Dynamic.AdjointDeterminantStructureStatement
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Structural package for the actual dynamic adjoint determinant -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The structural determinant inputs follow from actual connected reductivity
and representation of the dynamic subgroups on every scheme test. -/
theorem dynamicAdjointDeterminantStructure :
    DynamicAdjointDeterminantStructureStatement.{u} := by
  intro k _ G hG χ P M U iP iM iU hP hM hU
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hPc := Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP
  have hMc := Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hM
  have hUc := Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent χ hU
  let hPa : IsAffineHom P.X.hom := hPc.isAffineHom
  let hMa : IsAffineHom M.X.hom := hMc.isAffineHom
  let hUa : IsAffineHom U.X.hom := hUc.isAffineHom
  let : LocallyOfFiniteType P.X.hom := hPc.locallyOfFiniteType
  let : LocallyOfFiniteType M.X.hom := hMc.locallyOfFiniteType
  let : LocallyOfFiniteType U.X.hom := hUc.locallyOfFiniteType
  refine ⟨hPa, hMa, hUa, hPc, hMc, hUc,
    (dynamicSmooth k G χ P iP).1 hP, (dynamicSmooth k G χ M iM).2.1 hM,
    (dynamicSmooth k G χ U iU).2.2 hU, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  exact ⟨Module.finrank k (Additive (lieKernel U k)), ⟨Lie.finiteCoordinates U⟩⟩

end Langlands.GroupScheme
