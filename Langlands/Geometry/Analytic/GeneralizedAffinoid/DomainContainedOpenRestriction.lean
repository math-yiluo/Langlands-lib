import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainOpenImmersion

/-! # Intrinsic and ambient restrictions on contained ordinary opens -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory RationalChart TopologicalSpace Topology Opposite
open AlgebraicGeometry

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (d : Domain K A)

/-- The entire intrinsic inverse image of an ambient ordinary open. -/
abbrev preimageOpen (U : Opens (BanachSpectrum A)) : Opens (BanachSpectrum d.algebra) :=
  (Opens.map (openSpectrumMap d.baseMap)).obj U

/-- The original structural spectral map restricted to the inverse image. -/
def spectrumMapOnOpen (U : Opens (BanachSpectrum A)) :
    (Opens.toTopCat (TopCat.of (BanachSpectrum d.algebra))).obj (d.preimageOpen U) ⟶
      TopCat.of (BanachSpectrum A) :=
  (Opens.inclusion' (X := TopCat.of (BanachSpectrum d.algebra)) (d.preimageOpen U)) ≫ openSpectrumMap d.baseMap

/-- A contained ordinary open is exactly the image of its intrinsic inverse image. -/
theorem spectrumMapOnOpen_range (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    Set.range (d.spectrumMapOnOpen U) = (U : Set (BanachSpectrum A)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    obtain ⟨y, hy⟩ := d.represents.2.1.symm ▸ hU hx
    exact ⟨⟨y, show BanachSpectrum.comap d.baseMap.toBoundedRingHom y ∈
      (U : Set (BanachSpectrum A)) from hy.symm ▸ hx⟩, hy⟩

/-- No openness of the entire domain is required for this restricted open embedding. -/
theorem spectrumMapOnOpen_isOpenEmbedding (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    IsOpenEmbedding (d.spectrumMapOnOpen U) :=
  ⟨(spectrumEmbedding K A d).isEmbedding.comp
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra)) (d.preimageOpen U)).isEmbedding,
    d.spectrumMapOnOpen_range U hU ▸ U.isOpen⟩

/-- Restrict the actual intrinsic algebra sheaf before applying the original morphism. -/
def algebraSheafedSpaceMapOnOpen (U : Opens (BanachSpectrum A)) :
    (algebraSheafedSpace K d.algebra).restrict (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra)) (d.preimageOpen U)) ⟶
      algebraSheafedSpace K A :=
  (algebraSheafedSpace K d.algebra).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra)) (d.preimageOpen U)) ≫
    algebraSheafedSpaceMap d.baseMap

/-- On every ambient open contained in U, both components of the actual
restricted composite are invertible. -/
theorem algebraSheafedSpaceMapOnOpen_app_isIso (U W : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) (hW : W ≤ U) :
    IsIso ((d.algebraSheafedSpaceMapOnOpen U).hom.c.app (op W)) := by
  change IsIso ((openAlgebraPresheafMap d.baseMap).app (op W) ≫
    ((algebraSheafedSpace K d.algebra).ofRestrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra)) (d.preimageOpen U))).hom.c.app (op (d.preimageOpen W)))
  apply IsIso.comp_isIso'
  · exact d.openAlgebraPresheafMap_app_isIso W (fun x hx => hU (hW hx))
  · let := PresheafedSpace.IsOpenImmersion.ofRestrict
      (algebraSheafedSpace K d.algebra).toPresheafedSpace
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
        (d.preimageOpen U))
    apply PresheafedSpace.IsOpenImmersion.isIso_of_subset
      ((algebraSheafedSpace K d.algebra).toPresheafedSpace.ofRestrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
          (d.preimageOpen U))) (d.preimageOpen W)
    rintro y hy
    exact ⟨⟨y, hW hy⟩, rfl⟩

/-- The original algebra-sheaf morphism restricted over a contained ordinary
open is an actual open immersion with image that open. -/
theorem algebraSheafedSpaceMapOnOpen_isOpenImmersion (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    SheafedSpace.IsOpenImmersion (d.algebraSheafedSpaceMapOnOpen U) where
  base_open := d.spectrumMapOnOpen_isOpenEmbedding U hU
  c_iso W := d.algebraSheafedSpaceMapOnOpen_app_isIso U _ hU (by
    rintro x ⟨y, _, rfl⟩
    exact y.property)

/-- Compare the full intrinsic inverse image with the ordinary ambient restriction. -/
def algebraSheafedSpaceContainedOpenIso (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    (algebraSheafedSpace K d.algebra).restrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
        (d.preimageOpen U)) ≅
      (algebraSheafedSpace K A).restrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U) := by
  let := d.algebraSheafedSpaceMapOnOpen_isOpenImmersion U hU
  let : PresheafedSpace.IsOpenImmersion
      ((algebraSheafedSpace K A).ofRestrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U)).hom :=
    PresheafedSpace.IsOpenImmersion.ofRestrict _ _
  apply SheafedSpace.isoMk
  apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    (d.algebraSheafedSpaceMapOnOpen U).hom
    ((algebraSheafedSpace K A).ofRestrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U)).hom
  exact (d.spectrumMapOnOpen_range U hU).trans Subtype.range_val.symm

/-- The comparison factors the actual restricted structural morphism. -/
@[reassoc]
theorem algebraSheafedSpaceContainedOpenIso_hom_ofRestrict
    (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    (d.algebraSheafedSpaceContainedOpenIso U hU).hom ≫
      (algebraSheafedSpace K A).ofRestrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U) =
      d.algebraSheafedSpaceMapOnOpen U := by
  let := d.algebraSheafedSpaceMapOnOpen_isOpenImmersion U hU
  let : PresheafedSpace.IsOpenImmersion
      ((algebraSheafedSpace K A).ofRestrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U)).hom :=
    PresheafedSpace.IsOpenImmersion.ofRestrict _ _
  apply InducedCategory.hom_ext
  exact PresheafedSpace.IsOpenImmersion.lift_fac
    ((algebraSheafedSpace K A).ofRestrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U)).hom
    (d.algebraSheafedSpaceMapOnOpen U).hom
    (le_of_eq ((d.spectrumMapOnOpen_range U hU).trans Subtype.range_val.symm))

/-- Restrict the actual intrinsic ring sheaf before applying the original morphism. -/
def ringSheafedSpaceMapOnOpen (U : Opens (BanachSpectrum A)) :
    (ringSheafedSpace K d.algebra).restrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
        (d.preimageOpen U)) ⟶ ringSheafedSpace K A :=
  (ringSheafedSpace K d.algebra).ofRestrict
    (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
      (d.preimageOpen U)) ≫ ringSheafedSpaceMap d.baseMap

/-- Scalar forgetting preserves the invertible components of the actual composite. -/
theorem ringSheafedSpaceMapOnOpen_app_isIso (U W : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) (hW : W ≤ U) :
    IsIso ((d.ringSheafedSpaceMapOnOpen U).hom.c.app (op W)) := by
  let := d.algebraSheafedSpaceMapOnOpen_app_isIso U W hU hW
  change IsIso ((forget₂ (CommAlgCat K) CommRingCat.{u}).map
    ((d.algebraSheafedSpaceMapOnOpen U).hom.c.app (op W)))
  infer_instance

/-- The ring-sheaf morphism over a contained ordinary open is an open immersion. -/
theorem ringSheafedSpaceMapOnOpen_isOpenImmersion (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    SheafedSpace.IsOpenImmersion (d.ringSheafedSpaceMapOnOpen U) where
  base_open := d.spectrumMapOnOpen_isOpenEmbedding U hU
  c_iso W := d.ringSheafedSpaceMapOnOpen_app_isIso U _ hU (by
    rintro x ⟨y, _, rfl⟩
    exact y.property)

/-- The intrinsic and ambient ring sheaves agree on contained ordinary opens. -/
def ringSheafedSpaceContainedOpenIso (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    (ringSheafedSpace K d.algebra).restrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
        (d.preimageOpen U)) ≅
      (ringSheafedSpace K A).restrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U) := by
  let := d.ringSheafedSpaceMapOnOpen_isOpenImmersion U hU
  let : PresheafedSpace.IsOpenImmersion
      ((ringSheafedSpace K A).ofRestrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U)).hom :=
    PresheafedSpace.IsOpenImmersion.ofRestrict _ _
  apply SheafedSpace.isoMk
  apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    (d.ringSheafedSpaceMapOnOpen U).hom
    ((ringSheafedSpace K A).ofRestrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U)).hom
  exact (d.spectrumMapOnOpen_range U hU).trans Subtype.range_val.symm

@[reassoc]
theorem ringSheafedSpaceContainedOpenIso_hom_ofRestrict
    (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    (d.ringSheafedSpaceContainedOpenIso U hU).hom ≫
      (ringSheafedSpace K A).ofRestrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U) =
      d.ringSheafedSpaceMapOnOpen U := by
  let := d.ringSheafedSpaceMapOnOpen_isOpenImmersion U hU
  let : PresheafedSpace.IsOpenImmersion
      ((ringSheafedSpace K A).ofRestrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U)).hom :=
    PresheafedSpace.IsOpenImmersion.ofRestrict _ _
  apply InducedCategory.hom_ext
  exact PresheafedSpace.IsOpenImmersion.lift_fac
    ((ringSheafedSpace K A).ofRestrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U)).hom
    (d.ringSheafedSpaceMapOnOpen U).hom
    (le_of_eq ((d.spectrumMapOnOpen_range U hU).trans Subtype.range_val.symm))

/-- Restrict the genuine locally ringed-space morphism, preserving its stalk locality. -/
def locallyRingedSpaceMapOnOpen (U : Opens (BanachSpectrum A)) :
    (locallyRingedSpace K d.algebra).restrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
        (d.preimageOpen U)) ⟶ locallyRingedSpace K A :=
  (locallyRingedSpace K d.algebra).ofRestrict
    (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
      (d.preimageOpen U)) ≫ locallyRingedSpaceMap d.baseMap

/-- No openness assumption on the entire full-domain locus is needed. -/
theorem locallyRingedSpaceMapOnOpen_isOpenImmersion (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    LocallyRingedSpace.IsOpenImmersion (d.locallyRingedSpaceMapOnOpen U) :=
  d.ringSheafedSpaceMapOnOpen_isOpenImmersion U hU

/-- The full intrinsic inverse image and the ambient restriction are isomorphic
as actual locally ringed spaces. -/
def locallyRingedSpaceContainedOpenIso (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    (locallyRingedSpace K d.algebra).restrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
        (d.preimageOpen U)) ≅
      (locallyRingedSpace K A).restrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U) :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (d.ringSheafedSpaceContainedOpenIso U hU)

/-- The locally ringed-space comparison is over the original ambient space. -/
@[reassoc]
theorem locallyRingedSpaceContainedOpenIso_hom_ofRestrict
    (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    (d.locallyRingedSpaceContainedOpenIso U hU).hom ≫
      (locallyRingedSpace K A).ofRestrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A)) U) =
      d.locallyRingedSpaceMapOnOpen U := by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  exact d.ringSheafedSpaceContainedOpenIso_hom_ofRestrict U hU

/-- In particular, every full domain has this ordinary restriction comparison
over the interior of its represented locus. -/
abbrev locallyRingedSpaceInteriorIso :
    (locallyRingedSpace K d.algebra).restrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
        (d.preimageOpen ⟨interior d.locus, isOpen_interior⟩)) ≅
      (locallyRingedSpace K A).restrict
        (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum A))
          ⟨interior d.locus, isOpen_interior⟩) :=
  d.locallyRingedSpaceContainedOpenIso _ interior_subset

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
