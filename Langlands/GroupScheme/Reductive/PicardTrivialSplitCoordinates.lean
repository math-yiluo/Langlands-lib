import Langlands.GroupScheme.Reductive.ConnectedRootDatum
import Langlands.GroupScheme.Reductive.PicardRootWeightLines
import Langlands.GroupScheme.Reductive.SuppliedTorusLocalSplitting
import Langlands.GroupScheme.RelativeLevi.SplitBorelVectorSeriesProof

/-! # Split coordinates over a connected affine base with trivial Picard group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R] [ConnectedSpace (Spec (CommRingCat.of R))]
  (hPic : ∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle (Spec (CommRingCat.of R)),
    Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial
      (Spec (CommRingCat.of R))))
  (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)

include hPic hG hi hmax

/-- The supplied coordinate maximal torus is globally split, with one full
root datum and free actual root-weight modules over the original ring. -/
theorem hasSplitMaximalTorusCoordinates_of_connected_of_lineBundlesTrivial :
    letI := hG.isAffineHom
    HasSplitMaximalTorusCoordinates (T := splitTorus.commGroupScheme _ I) i := by
  let := hG.isAffineHom
  obtain ⟨J, P, hP⟩ := exists_fibrewiseRootDatumOf_of_connected I G hG i hmax
  refine ⟨I, inferInstance, Iso.refl _, ?_⟩
  simp only [Iso.refl_hom, Category.id_comp]
  exact ⟨hi, hmax, J, P, hP,
    rootWeightSpace_nonempty_linearEquiv_of_lineBundlesTrivial hPic I G hG i hmax P hP⟩

/-- A supplied split maximal torus over a connected affine base with trivial
scheme Picard group lies in a split Borel with a finite vector-quotient kernel
series. -/
theorem hasSplitBorelVectorSeries_of_connected_of_lineBundlesTrivial :
    HasSplitBorelVectorSeries i := by
  let := hG.isAffineHom
  obtain ⟨J, P, hP⟩ := exists_fibrewiseRootDatumOf_of_connected I G hG i hmax
  exact splitBorelVectorSeries R G hG I i J P hi hmax hP
    (rootWeightSpace_nonempty_linearEquiv_of_lineBundlesTrivial hPic I G hG i hmax P hP)


/-- Choose the actual Borel subgroup group scheme supplied by the split Borel
vector-series construction over the original affine base. -/
def picardSplitBorel : GroupScheme (Spec (CommRingCat.of R)) :=
  (hasSplitBorelVectorSeries_of_connected_of_lineBundlesTrivial hPic I G hG i hi hmax).choose

end Langlands.GroupScheme
