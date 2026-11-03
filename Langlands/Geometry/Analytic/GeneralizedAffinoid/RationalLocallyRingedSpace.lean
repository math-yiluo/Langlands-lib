import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenLocalRing
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # The locally ringed space of an actual affinoid spectrum -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

local instance : PreservesLimits (forget₂ (CommAlgCat K) CommRingCat.{u}) := by
  change PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of K)).functor ⋙
    Under.forget (CommRingCat.of K))
  infer_instance

local instance : PreservesFilteredColimits (forget₂ (CommAlgCat K) CommRingCat.{u}) where
  preserves_filtered_colimits J _ _ := by
    have : IsConnected J := IsFiltered.isConnected J
    change PreservesColimitsOfShape J ((commAlgCatEquivUnder (CommRingCat.of K)).functor ⋙
      Under.forget (CommRingCat.of K))
    infer_instance

/-- The original compatible-family presheaf, with scalars forgotten. -/
def openRingPresheaf (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    TopCat.Presheaf CommRingCat.{u} (TopCat.of (BanachSpectrum A)) :=
  openAlgebraPresheaf K A ⋙ forget₂ (CommAlgCat K) CommRingCat

/-- The sheaf law follows by preservation of limits under forgetting scalars. -/
theorem openRingPresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (openRingPresheaf K A) :=
  CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _
    (forget₂ (CommAlgCat K) CommRingCat.{u}) openAlgebraPresheaf_isSheaf

/-- The commutative-ring sheaf has the same concrete sections and restrictions. -/
def ringSheafedSpace (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    AlgebraicGeometry.SheafedSpace CommRingCat.{u} where
  carrier := TopCat.of (BanachSpectrum A)
  presheaf := openRingPresheaf K A
  IsSheaf := openRingPresheaf_isSheaf

/-- Forgetting scalars commutes with the actual ordinary-open stalk colimit. -/
def openStalkRingIso (x : BanachSpectrum A) :
    (forget₂ (CommAlgCat K) CommRingCat.{u}).obj (openStalk x) ≅
      TopCat.Presheaf.stalk (openRingPresheaf K A) x :=
  preservesColimitIso (forget₂ (CommAlgCat K) CommRingCat.{u})
    ((OpenNhds.inclusion (X := TopCat.of (BanachSpectrum A)) x).op ⋙
      openAlgebraPresheaf K A)

/-- The canonical stalk comparison retains the original germ maps. -/
@[reassoc (attr := simp)]
theorem openGerm_openStalkRingIso (U : Opens (BanachSpectrum A))
    (x : BanachSpectrum A) (hx : x ∈ U) :
    (forget₂ (CommAlgCat K) CommRingCat.{u}).map (openGerm U x hx) ≫
      (openStalkRingIso x).hom =
      TopCat.Presheaf.germ (openRingPresheaf K A) U x hx :=
  ι_preservesColimitIso_hom _ _ _

/-- The actual affinoid spectrum, concrete structure sheaf and proved local stalks. -/
def locallyRingedSpace (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    AlgebraicGeometry.LocallyRingedSpace where
  toSheafedSpace := ringSheafedSpace K A
  isLocalRing x := by
    let : IsLocalRing
        ((forget₂ (CommAlgCat K) CommRingCat.{u}).obj (openStalk x)) :=
      openStalk_isLocalRing x
    exact (openStalkRingIso x).commRingCatIsoToRingEquiv.isLocalRing

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
