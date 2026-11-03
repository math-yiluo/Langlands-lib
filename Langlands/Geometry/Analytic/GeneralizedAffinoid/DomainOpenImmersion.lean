import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainOpenPullbackComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenMorphism
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! # Open full affinoid domains as actual open immersions -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory RationalChart TopologicalSpace Topology Opposite
open AlgebraicGeometry

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (d : Domain K A)

/-- The actual algebra-sheaf component is invertible on every ambient open
contained in the domain, without an openness assumption on the whole locus. -/
theorem openAlgebraPresheafMap_app_isIso (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    IsIso ((openAlgebraPresheafMap d.baseMap).app (op U)) := by
  change IsIso (CommAlgCat.ofHom (OpenSections.pullback d.baseMap U))
  rw [← d.openSectionsEquiv_toAlgHom U hU]
  exact (CommAlgCat.isoMk (d.openSectionsEquiv U hU)).isIso_hom

/-- If its represented locus is open, the original structural spectrum map
is an open embedding. -/
theorem spectrumMap_isOpenEmbedding (hd : IsOpen d.locus) :
    IsOpenEmbedding (openSpectrumMap d.baseMap) :=
  ⟨(spectrumEmbedding K A d).isEmbedding, d.represents.2.1.symm ▸ hd⟩

/-- The constructed algebra-sheaf morphism of an open full domain is an
open immersion, with the original bounded-map pullback as its sheaf map. -/
theorem algebraSheafedSpaceMap_isOpenImmersion (hd : IsOpen d.locus) :
    SheafedSpace.IsOpenImmersion (algebraSheafedSpaceMap d.baseMap) where
  base_open := d.spectrumMap_isOpenEmbedding hd
  c_iso U := d.openAlgebraPresheafMap_app_isIso _ (by
    rintro x ⟨y, _, rfl⟩
    exact d.represents.hasImageIn y)

/-- The actual intrinsic algebra sheaf is isomorphic to the ambient sheaf
restricted along the structural open embedding. -/
def algebraSheafedSpaceRestrictIso (hd : IsOpen d.locus) :
    algebraSheafedSpace K d.algebra ≅
      (algebraSheafedSpace K A).restrict (d.spectrumMap_isOpenEmbedding hd) := by
  let := d.algebraSheafedSpaceMap_isOpenImmersion hd
  exact SheafedSpace.IsOpenImmersion.isoRestrict (algebraSheafedSpaceMap d.baseMap)

/-- The comparison keeps the intrinsic spectrum as its carrier. -/
@[simp]
theorem algebraSheafedSpaceRestrictIso_hom_base (hd : IsOpen d.locus) :
    (d.algebraSheafedSpaceRestrictIso hd).hom.hom.base =
      𝟙 (TopCat.of (BanachSpectrum d.algebra)) := rfl

/-- The restriction comparison factors the original actual algebra-sheaf
morphism through the canonical inclusion of the restricted space. -/
@[reassoc]
theorem algebraSheafedSpaceRestrictIso_hom_ofRestrict (hd : IsOpen d.locus) :
    (d.algebraSheafedSpaceRestrictIso hd).hom ≫
      (algebraSheafedSpace K A).ofRestrict (d.spectrumMap_isOpenEmbedding hd) =
        algebraSheafedSpaceMap d.baseMap := by
  let := d.algebraSheafedSpaceMap_isOpenImmersion hd
  exact SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict
    (algebraSheafedSpaceMap d.baseMap)

/-- The scalar-forgotten actual component is invertible on contained opens. -/
theorem openRingPresheafMap_app_isIso (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    IsIso ((ringSheafedSpaceMap d.baseMap).hom.c.app (op U)) := by
  let := d.openAlgebraPresheafMap_app_isIso U hU
  change IsIso ((forget₂ (CommAlgCat K) CommRingCat.{u}).map
    ((openAlgebraPresheafMap d.baseMap).app (op U)))
  infer_instance

/-- Forgetting scalars retains the open immersion of the original ring
sheaves and the same structural spectrum map. -/
theorem ringSheafedSpaceMap_isOpenImmersion (hd : IsOpen d.locus) :
    SheafedSpace.IsOpenImmersion (ringSheafedSpaceMap d.baseMap) where
  base_open := d.spectrumMap_isOpenEmbedding hd
  c_iso U := d.openRingPresheafMap_app_isIso _ (by
    rintro x ⟨y, _, rfl⟩
    exact d.represents.hasImageIn y)

/-- The intrinsic commutative-ring sheaf is the ambient restriction. -/
def ringSheafedSpaceRestrictIso (hd : IsOpen d.locus) :
    ringSheafedSpace K d.algebra ≅
      (ringSheafedSpace K A).restrict (d.spectrumMap_isOpenEmbedding hd) := by
  let := d.ringSheafedSpaceMap_isOpenImmersion hd
  exact SheafedSpace.IsOpenImmersion.isoRestrict (ringSheafedSpaceMap d.baseMap)

@[reassoc]
theorem ringSheafedSpaceRestrictIso_hom_ofRestrict (hd : IsOpen d.locus) :
    (d.ringSheafedSpaceRestrictIso hd).hom ≫
      (ringSheafedSpace K A).ofRestrict (d.spectrumMap_isOpenEmbedding hd) =
        ringSheafedSpaceMap d.baseMap := by
  let := d.ringSheafedSpaceMap_isOpenImmersion hd
  exact SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict
    (ringSheafedSpaceMap d.baseMap)

/-- The previously constructed morphism, with locality proved on actual
ordinary-open stalks, is an open immersion for an open full-domain locus. -/
theorem locallyRingedSpaceMap_isOpenImmersion (hd : IsOpen d.locus) :
    LocallyRingedSpace.IsOpenImmersion (locallyRingedSpaceMap d.baseMap) :=
  d.ringSheafedSpaceMap_isOpenImmersion hd

/-- The intrinsic locally ringed space of an open full domain is isomorphic
to the restriction of the original ambient locally ringed space. -/
def locallyRingedSpaceRestrictIso (hd : IsOpen d.locus) :
    locallyRingedSpace K d.algebra ≅
      (locallyRingedSpace K A).restrict (d.spectrumMap_isOpenEmbedding hd) := by
  let := d.locallyRingedSpaceMap_isOpenImmersion hd
  exact LocallyRingedSpace.IsOpenImmersion.isoRestrict (locallyRingedSpaceMap d.baseMap)

/-- The locally ringed-space comparison likewise has the identity base map. -/
@[simp]
theorem locallyRingedSpaceRestrictIso_hom_base (hd : IsOpen d.locus) :
    (d.locallyRingedSpaceRestrictIso hd).hom.base =
      𝟙 (TopCat.of (BanachSpectrum d.algebra)) := rfl

/-- The comparison is over the ambient locally ringed space through the
original actual bounded-map morphism. -/
@[reassoc]
theorem locallyRingedSpaceRestrictIso_hom_ofRestrict (hd : IsOpen d.locus) :
    (d.locallyRingedSpaceRestrictIso hd).hom ≫
      (locallyRingedSpace K A).ofRestrict (d.spectrumMap_isOpenEmbedding hd) =
        locallyRingedSpaceMap d.baseMap := by
  let := d.locallyRingedSpaceMap_isOpenImmersion hd
  exact LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict
    (locallyRingedSpaceMap d.baseMap)

/-- The actual ordinary-open algebra-stalk maps of an open full domain are
isomorphisms. -/
theorem openStalkMap_isIso (hd : IsOpen d.locus) (y : BanachSpectrum d.algebra) :
    IsIso (openStalkMap d.baseMap y) := by
  let := d.algebraSheafedSpaceMap_isOpenImmersion hd
  exact SheafedSpace.IsOpenImmersion.stalk_iso (algebraSheafedSpaceMap d.baseMap) y

/-- The actual ordinary-open ring-stalk maps are likewise isomorphisms. -/
theorem openRingStalkMap_isIso (hd : IsOpen d.locus) (y : BanachSpectrum d.algebra) :
    IsIso (openRingStalkMap d.baseMap y) := by
  let := d.ringSheafedSpaceMap_isOpenImmersion hd
  exact SheafedSpace.IsOpenImmersion.stalk_iso (ringSheafedSpaceMap d.baseMap) y

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
