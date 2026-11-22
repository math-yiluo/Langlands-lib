import Langlands.Geometry.Analytic.AffinoidEtaleImageRecognition
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleFromSourceDescent
import Langlands.Geometry.Analytic.SpaceAnalytificationSeparatedness

/-! # Analytification detects étale morphisms of algebraic spaces -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open SaturatedAtlasPresentation AffinoidAtlasPresentation AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

private def fullRecognitionComparison (A : SaturatedAtlasPresentation.{u, u, u} K) :
    localizationFunctor.obj A ≅ localizationFunctor.obj (ofFullRecognition A.presentation) :=
  (localizationFunctor.mapIso A.saturationIso).symm ≪≫ fullRecognitionIso A.presentation

private abbrev fullRecognitionStrongMap {A B : SaturatedAtlasPresentation.{u, u, u} K}
    (g : A ⟶ B) : StrongHom A.presentation.saturatedPresentation B.presentation.saturatedPresentation :=
  ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map g)

set_option backward.isDefEq.respectTransparency false in
private theorem fullRecognitionComparison_naturality {A B : SaturatedAtlasPresentation.{u, u, u} K}
    (g : A ⟶ B) : (fullRecognitionComparison A).hom ≫ (fullRecognitionStrongMap g).fullRecognitionLocalizedHom =
      localizationFunctor.map g ≫ (fullRecognitionComparison B).hom := by
  let gS : ofSaturation A.presentation ⟶ ofSaturation B.presentation := fullRecognitionStrongMap g
  have h : A.saturationIso.inv ≫ gS = g ≫ B.saturationIso.inv := by
    change A.saturationIso.inv ≫ ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map g) = _
    rw [saturationExtension_eq_conjugate g]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change (localizationFunctor.map A.saturationIso.inv ≫ (fullRecognitionIso A.presentation).hom) ≫
    (fullRecognitionStrongMap g).fullRecognitionLocalizedHom =
      localizationFunctor.map g ≫ localizationFunctor.map B.saturationIso.inv ≫
        (fullRecognitionIso B.presentation).hom
  rw [Category.assoc, fullRecognitionIso_naturality, ← Category.assoc,
    ← localizationFunctor.map_comp, h, localizationFunctor.map_comp, Category.assoc]

set_option maxHeartbeats 950000 in
set_option backward.isDefEq.respectTransparency false in
private theorem isEtaleAtAllPieces_of_affine_test
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hsX : IsSeparated X)
    (htX : LocallyOfFiniteTypeOverBase X)
    {B : SaturatedAtlasPresentation.{u, u, u} K} {C : AffinoidAtlasPresentation.{u, u, u} K}
    {p : PointFamily K X (localizationFunctor.obj (ofFullRecognition B.presentation))}
    (hp : IsAnalytification K X _ p)
    (f : StrongHom B.presentation.saturatedPresentation C.saturatedPresentation)
    (z : B.presentation.space) {T : Type u} [CommRing T] [Algebra K T]
    (P : FinitePolynomialPresentation K T) (x : RingPoints K X T)
    (hx : AlgebraicSpace.IsEtale (pointHom K x))
    (hz : z ∈ range (localizedSpaceFunctor.map (p T P x)))
    (hc : etale (p T P x ≫ f.fullRecognitionLocalizedHom)) : f.IsEtaleAtAllPieces z := by
  let eB := fullRecognitionComparison B
  let test := p T P x
  let testOriginal := test ≫ eB.inv
  obtain ⟨A, s, hs, a, _, ha, _⟩ := exists_commonStrongNumerators
    (T := AffineAnalytification.saturated K P) testOriginal testOriginal
  let q := fullRecognitionStrongMap a
  let eA := (fullRecognitionComparison A).symm ≪≫ localizedQuasiIso s hs
  have hq : q.fullRecognitionLocalizedHom = eA.hom ≫ test := by
    apply (cancel_epi (fullRecognitionComparison A).hom).mp
    calc
      _ = localizationFunctor.map a ≫ eB.hom := fullRecognitionComparison_naturality a
      _ = (localizationFunctor.map s ≫ testOriginal) ≫ eB.hom :=
        congrArg (· ≫ eB.hom) ha.symm
      _ = _ := by
        change (localizationFunctor.map s ≫ test ≫ eB.inv) ≫ eB.hom =
          (fullRecognitionComparison A).hom ≫
            ((fullRecognitionComparison A).inv ≫ localizationFunctor.map s) ≫ test
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hqEtale : etale q.fullRecognitionLocalizedHom := by
    rw [hq]
    exact ((etale (K := K)).cancel_left_of_respectsIso eA.hom test).mpr (hp.etale_map P x hx)
  have hqcEtale : etale (q.fullRecognitionLocalizedHom ≫ f.fullRecognitionLocalizedHom) := by
    rw [hq, Category.assoc]
    exact ((etale (K := K)).cancel_left_of_respectsIso eA.hom _).mpr hc
  have hqStrong := (etale_fullRecognition_iff q).mp hqEtale
  have hqcStrong : (q.saturatedComp f A.presentation.atlas.saturatedAtlas_hasAllLocalDomains
      B.presentation.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAllPieces :=
    (etale_fullRecognition_iff _).mp ((congrArg (fun m => etale m) (fullRecognition_comp q f)).mp hqcEtale)
  have hPoint (R : PresentedAffinoidAlgebra K)
      (r : localizedAffinoidSpectrum R ⟶ localizationFunctor.obj (ofFullRecognition A.presentation)) :
      ∃ xR : RingPoints K X R, affinoidPointHom hp hsX htX R xR = r ≫ q.fullRecognitionLocalizedHom := by
    obtain ⟨φ, hφ⟩ := (AffineAnalytification.localizedAffinoidHomEquiv K P R).surjective (r ≫ eA.hom)
    change AffineAnalytification.localizedAffinoidHom K P R φ = r ≫ eA.hom at hφ
    refine ⟨RingPoints.changeRing φ x, (affinoidPointHom_test hp hsX htX R P φ x).trans ?_⟩
    change AffineAnalytification.localizedAffinoidHom K P R φ ≫ test = r ≫ q.fullRecognitionLocalizedHom
    rw [hφ, Category.assoc, ← hq]
  obtain ⟨t, ht⟩ := hz
  let eAspace := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eA)
  obtain ⟨v, hv⟩ := eAspace.surjective t
  have hvq : q.baseMap v = z := by
    have hvq' : localizedSpaceFunctor.map q.fullRecognitionLocalizedHom v = z := by
      rw [hq, localizedSpaceFunctor.map_comp, TopCat.comp_app]
      change localizedSpaceFunctor.map test (eAspace v) = z
      exact (congrArg (localizedSpaceFunctor.map test) hv).trans ht
    rw [localizedSpaceFunctor_map_fullRecognition q] at hvq'
    exact hvq'
  let : T2Space B.presentation.space := hp.t2Space_of_isSeparated hsX
  let N := finiteEtaleSourceNeighborhoods hqStrong hqcStrong v
  exact hvq ▸ N.isEtaleAtAllPieces hqStrong
    (exists_recognized_finiteEtaleImage hp hsX htX hqStrong N hPoint)

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency false in
/-- Étaleness descends along the actual étale affine test family of a
separated locally finite type algebraic space. -/
theorem etale_of_affine_test_composites
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hsX : IsSeparated X)
    (htX : LocallyOfFiniteTypeOverBase X)
    {Y Z : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}
    (hp : IsAnalytification K X Y p) (F : Y ⟶ Z)
    (h : ∀ {T : Type u} [CommRing T] [Algebra K T] (P : FinitePolynomialPresentation K T)
      (x : RingPoints K X T), AlgebraicSpace.IsEtale (pointHom K x) → etale (p T P x ≫ F)) :
    etale F := by
  obtain ⟨B₀, rfl⟩ := localizedObjectEquiv.surjective Y
  obtain ⟨C, rfl⟩ := localizedObjectEquiv.surjective Z
  obtain ⟨B, s, hs, b, _, hb, _⟩ := exists_commonStrongNumerators F F
  let eY := (localizedQuasiIso s hs).symm ≪≫ fullRecognitionComparison B
  let eZ := fullRecognitionComparison C
  let f := fullRecognitionStrongMap b
  have hF : eY.hom ≫ f.fullRecognitionLocalizedHom = F ≫ eZ.hom := by
    change ((localizedQuasiIso s hs).inv ≫ (fullRecognitionComparison B).hom) ≫
      f.fullRecognitionLocalizedHom = F ≫ eZ.hom
    rw [Category.assoc, fullRecognitionComparison_naturality b, ← hb, Category.assoc]
    exact (localizedQuasiIso s hs).inv_hom_id_assoc (F ≫ eZ.hom)
  let pB : PointFamily K X (localizationFunctor.obj (ofFullRecognition B.presentation)) :=
    fun T _ _ P x => p T P x ≫ eY.hom
  have hpB : IsAnalytification K X _ pB := hp.comp_iso eY
  have hf : f.IsEtaleAllPieces := by
    intro z
    obtain ⟨T, _, _, P, x, hx, hz⟩ := hpB.jointly_surjective z
    have hB : etale (pB T P x ≫ f.fullRecognitionLocalizedHom) := by
      change etale ((p T P x ≫ eY.hom) ≫ f.fullRecognitionLocalizedHom)
      rw [Category.assoc, hF, ← Category.assoc]
      exact ((etale (K := K)).cancel_right_of_respectsIso _ eZ.hom).mpr (h P x hx)
    exact isEtaleAtAllPieces_of_affine_test hsX htX hpB f z P x hx hz hB
  have hF' : etale (F ≫ eZ.hom) := by
    rw [← hF]
    exact ((etale (K := K)).cancel_left_of_respectsIso eY.hom _).mpr ((etale_fullRecognition_iff f).mpr hf)
  exact ((etale (K := K)).cancel_right_of_respectsIso _ eZ.hom).mp hF'

/-- The unchanged comparison for algebraic-space analytification, in every universe. -/
theorem spaceAnalytificationEtale : SpaceAnalytificationEtaleStatement.{u} := by
  intro K _ _ _ X' X f hsX' htX' hsX htX Y' Y p' p hp' hp F hF
  constructor
  · intro hf
    apply etale_of_affine_test_composites hsX' htX' hp' F
    intro T _ _ P x hx
    rw [hF]
    apply hp.etale_map
    rw [pointHom_map]
    exact hf _ _ hx
  · exact isEtaleMorphism_of_etale K f htX' hsX htX hp' hp F hF

end Langlands.Analytic.SpaceAnalytification
