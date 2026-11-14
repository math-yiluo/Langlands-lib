import Langlands.BruhatTits.RationalPoints.BoundedOpenNormalizerStatement
import Langlands.BruhatTits.RationalPoints.DenseBoundedNormalizerAdjointStatement
import Langlands.BruhatTits.RationalPoints.AdjointNormKernelBoundedPreimageStatement
import Langlands.GroupScheme.Adjoint.ExistenceProof
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.AlgebraicGeometry.PointTopology.RationalLocalDensityProof

/-! # Reduction of KP 2.2.16 to two adjoint boundedness statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.RationalPoints

/-- An analytically open subgroup of a smooth connected affine group over
a nonarchimedean local field is a dense actual rational-point family. -/
theorem hasDenseRationalPointFamily_subgroup_of_isOpen
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (H : Subgroup (rationalPoints G))
    (hH : letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsOpen (H : Set (rationalPoints G))) :
    HasDenseRationalPointFamily H.subtype := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : IsIntegral G.X.left :=
    CharacterLatticeProof.isIntegral_of_smooth F G.X.hom
  have hd := (rationalLocalDensity F G.X).2
    (H : Set (rationalPoints G)) hH ⟨1, H.one_mem⟩
  apply hd.mono
  rintro x ⟨p, hp, rfl⟩
  exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, IsLocalRing.closedPoint F, rfl⟩

set_option linter.defProp false in
/-- The two adjoint boundedness inputs imply the exact unchanged target.
The inputs remain explicit mathematical obligations. -/
def boundedOpenNormalizer_of_adjoint_inputs
    (hNormalizer : DenseBoundedNormalizerAdjointStatement.{u})
    (hPreimage : AdjointNormKernelBoundedPreimageStatement.{u}) :
    BoundedOpenNormalizerStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  intro H hHb hHo
  obtain ⟨A, q, hq⟩ := adjointQuotientExistence F G hG
  let : IsAffineHom A.X.hom :=
    hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  have hd := hasDenseRationalPointFamily_subgroup_of_isOpen F G H hHo
  have hb := hNormalizer F G hG A q hq H hHb hd
  apply (hPreimage F G hG A q hq _ hb).mono
  intro g hg
  exact ⟨⟨g, hg.1, rfl⟩, hg.2⟩

end Langlands.BruhatTits.RationalPoints
