import Langlands.GroupScheme.Reductive.GeometricIsoSeparableStatement
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Reductive.LocalSplitGeometricIsoProof
import Langlands.GroupScheme.Reductive.SplitIsogenyRigidityReduction
import Langlands.GroupScheme.Torus.CommonFiniteGaloisSplitting
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Geometrically isomorphic reductive groups over a finite separable extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 23.28: geometrically isomorphic connected reductive groups
become isomorphic over a finite separable extension. -/
theorem reductiveGeometricIsoSeparable : ReductiveGeometricIsoSeparableStatement.{u} := by
  intro k _ G H hG hH ⟨e⟩
  let := hG.smooth
  let := hG.isAffineHom
  let := hH.smooth
  let := hH.isAffineHom
  obtain ⟨T, i, hi⟩ := maximalTorusExistence k G
  obtain ⟨U, j, hj⟩ := maximalTorusExistence k H
  let splitting := hi.1.commonFiniteGaloisSplitting hj.1
  let L := splitting.carrier
  let b := Spec.algebraMap k L
  let Gₗ := (baseChange b).obj G
  let Hₗ := (baseChange b).obj H
  have hGₗ : IsConnectedReductive Gₗ := hG.baseChange_of_algebraicExtension
  have hHₗ : IsConnectedReductive Hₗ := hH.baseChange_of_algebraicExtension
  let := hGₗ.smooth
  let := hGₗ.isAffineHom
  let := hHₗ.smooth
  let := hHₗ.isAffineHom
  have hiₗ := (maximalTorusBaseChange k L G T i hi.1 hi.2.1).mp hi
  have hjₗ := (maximalTorusBaseChange k L H U j hj.1 hj.2.1).mp hj
  let ι : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let : Algebra L (AlgebraicClosure k) := ι.toRingHom.toAlgebra
  let : IsScalarTower k L (AlgebraicClosure k) :=
    IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  let eG := baseChangeFieldTowerIso k L (AlgebraicClosure k) G
  let eH := baseChangeFieldTowerIso k L (AlgebraicClosure k) H
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    localSplitReductiveGeometricIso L Gₗ Hₗ hGₗ.isReductive hHₗ.isReductive
      ⟨(CommGroupScheme.baseChange b).obj T, (baseChange b).map i,
        splitting.split_left, hiₗ.2.1, hiₗ.isFibrewiseMaximalTorus⟩
      ⟨(CommGroupScheme.baseChange b).obj U, (baseChange b).map j,
        splitting.split_right, hjₗ.2.1, hjₗ.isFibrewiseMaximalTorus⟩
      (AlgebraicClosure k) ⟨eG.symm ≪≫ e ≪≫ eH⟩⟩

end Langlands.GroupScheme
