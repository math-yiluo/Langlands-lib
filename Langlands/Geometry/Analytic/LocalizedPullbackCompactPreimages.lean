import Langlands.Geometry.Analytic.FibreProductCompactPreimages
import Langlands.Geometry.Analytic.QuasiEtaleDomainChartCover
import Langlands.Geometry.Analytic.QuasiEtalePullbackSmallness
import Langlands.Geometry.Analytic.RecognizedLocalizedPullbacks

/-! # Compact inverse images of compatible factor pairs in localized pullbacks -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P A B X : LocalizedCategory.{u, v, v} (K := K)}

/-- The two underlying projections together as a continuous map. -/
def localizedProjectionPair (p : P ⟶ A) (q : P ⟶ B) :
    C(localizedSpaceFunctor.obj P, localizedSpaceFunctor.obj A × localizedSpaceFunctor.obj B) :=
  ⟨fun z => (localizedSpaceFunctor.map p z, localizedSpaceFunctor.map q z),
    (localizedSpaceFunctor.map p).hom.continuous.prodMk (localizedSpaceFunctor.map q).hom.continuous⟩

/-- A Hausdorff pullback point with compact preimages of compact compatible pairs. -/
def HasCompactPairPreimages (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ X) (g : B ⟶ X) : Prop :=
  T2Space (localizedSpaceFunctor.obj P) ∧
    ∀ S : Set (localizedSpaceFunctor.obj A × localizedSpaceFunctor.obj B),
      IsCompact S →
      (∀ z ∈ S, localizedSpaceFunctor.map f z.1 = localizedSpaceFunctor.map g z.2) →
      IsCompact (localizedProjectionPair p q ⁻¹' S)

private theorem point_square {P' A' : LocalizedCategory.{u, v, v} (K := K)}
    (p : P ⟶ A) (p' : P' ⟶ A') (eP : P ≅ P') (eA : A ≅ A')
    (hp : p ≫ eA.hom = eP.hom ≫ p') (z : localizedSpaceFunctor.obj P) :
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eA)) (localizedSpaceFunctor.map p z) =
      localizedSpaceFunctor.map p' ((TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eP)) z) := by
  have h := congrArg (fun φ : P ⟶ A' => localizedSpaceFunctor.map φ z) hp
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    TopCat.comp_app, TopCat.comp_app] at h
  exact h

private theorem HasCompactPairPreimages.of_iso
    {P' A' B' X' : LocalizedCategory.{u, v, v} (K := K)}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    {p' : P' ⟶ A'} {q' : P' ⟶ B'} {f' : A' ⟶ X'} {g' : B' ⟶ X'}
    (h : HasCompactPairPreimages p' q' f' g')
    (eP : P ≅ P') (eA : A ≅ A') (eB : B ≅ B') (eX : X ≅ X')
    (hp : p ≫ eA.hom = eP.hom ≫ p') (hq : q ≫ eB.hom = eP.hom ≫ q')
    (hf : f ≫ eX.hom = eA.hom ≫ f') (hg : g ≫ eX.hom = eB.hom ≫ g') :
    HasCompactPairPreimages p q f g := by
  let EP := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eP)
  let EA := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eA)
  let EB := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eB)
  let EX := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eX)
  let E := EA.prodCongr EB
  let : T2Space (localizedSpaceFunctor.obj P') := h.1
  refine ⟨EP.symm.t2Space, fun S hS hcond => ?_⟩
  have hcond' : ∀ z ∈ E '' S,
      localizedSpaceFunctor.map f' z.1 = localizedSpaceFunctor.map g' z.2 := by
    rintro _ ⟨z, hz, rfl⟩
    exact (point_square f f' eA eX hf z.1).symm.trans
      ((congrArg EX (hcond z hz)).trans (point_square g g' eB eX hg z.2))
  have hcompact := h.2 (E '' S) (hS.image E.continuous) hcond'
  have heq : EP ⁻¹' (localizedProjectionPair p' q' ⁻¹' (E '' S)) =
      localizedProjectionPair p q ⁻¹' S := by
    ext z
    have hpoint : E (localizedProjectionPair p q z) = localizedProjectionPair p' q' (EP z) :=
      Prod.ext (point_square p p' eP eA hp z) (point_square q q' eP eB hq z)
    change localizedProjectionPair p' q' (EP z) ∈ E '' S ↔ localizedProjectionPair p q z ∈ S
    rw [← hpoint]
    constructor
    · rintro ⟨w, hw, he⟩
      exact E.injective he ▸ hw
    · exact fun hz => ⟨_, hz, rfl⟩
  rw [← heq]
  exact EP.isCompact_preimage.mpr hcompact

private theorem hasCompactPairPreimages_smallFibreProduct
    {A B X : SaturatedAtlasPresentation.{u, v, v} K}
    [T2Space A.presentation.space] [T2Space B.presentation.space]
    (f : A ⟶ X) (g : B ⟶ X)
    [Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap f) (geometricCompatibleMap g)).Space] :
    HasCompactPairPreimages (localizationFunctor.map (smallFibreProductFst f g))
      (localizationFunctor.map (smallFibreProductSnd f g))
      (localizationFunctor.map f) (localizationFunctor.map g) := by
  let F := geometricCompatibleMap f
  let H := geometricCompatibleMap g
  let E := FibreProduct.smallSpaceHomeomorph F H A.hasAllLocalDomains
    B.hasAllLocalDomains X.hasAllLocalDomains
  let : T2Space (FibreProduct.chartSystem F H).Space :=
    FibreProduct.t2Space_chartSystem_of_factors F H
      A.hasAllLocalDomains B.hasAllLocalDomains X.hasAllLocalDomains
  refine ⟨E.t2Space, fun S hS hcond => ?_⟩
  change IsCompact (E.symm ⁻¹' (FibreProduct.projectionPair F H ⁻¹' S))
  exact E.symm.isCompact_preimage.mpr
    (FibreProduct.isCompact_preimage_projectionPair F H
      A.hasAllLocalDomains B.hasAllLocalDomains X.hasAllLocalDomains hS hcond)

private theorem hasCompactPairPreimages_of_strongQuasiEtale
    {A X : AffinoidAtlasPresentation.{u, v, v} K}
    {B : SaturatedAtlasPresentation.{u, v, v} K}
    {f : ofSaturation A ⟶ ofSaturation X} {g : B ⟶ ofSaturation X}
    {p : P ⟶ localizationFunctor.obj (ofSaturation A)} {q : P ⟶ localizationFunctor.obj B}
    [T2Space A.space] [T2Space B.presentation.space]
    (hP : IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g))
    (hf : IsQuasiEtale f) :
    HasCompactPairPreimages p q (localizationFunctor.map f) (localizationFunctor.map g) := by
  let F := recognitionMap f
  let H := recognitionMap g
  let : Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap F) (geometricCompatibleMap H)).Space :=
    small_recognition_fibreProductSpace_of_domainEtaleCharts f g (by
      intro y
      obtain ⟨s, _, hn, hs⟩ := hf.exists_local_domainEtale_charts y
      obtain ⟨V, hV, hy⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hn)
      obtain ⟨i, hi, hfactor⟩ := hs V hV
      exact ⟨i, hi.symm ▸ hy,
        by simpa only [CategoryTheory.Functor.map_comp, localizedDomainInclusion] using hfactor⟩)
  let eA := recognitionSourceIso f
  let eB := recognitionSourceIso g
  let eX := recognitionBaseIso (ofSaturation X)
  let : T2Space (localizedSpaceFunctor.obj (localizationFunctor.obj (ofSaturation A))) :=
    ‹T2Space A.space›
  let : T2Space (localizedSpaceFunctor.obj (localizationFunctor.obj B)) :=
    ‹T2Space B.presentation.space›
  let : T2Space (recognitionSource f).presentation.space :=
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eA)).t2Space
  let : T2Space (recognitionSource g).presentation.space :=
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eB)).t2Space
  let p' := p ≫ eA.hom
  let q' := q ≫ eB.hom
  have hP' : IsPullback p' q' (localizationFunctor.map F) (localizationFunctor.map H) := by
    apply hP.of_iso (Iso.refl _) eA eB eX
    · simp [p']
    · simp [q']
    · exact (recognitionMap_localized_square f).symm
    · exact (recognitionMap_localized_square g).symm
  let hmodel := smallFibreProduct_isPullback F H
  exact (hasCompactPairPreimages_smallFibreProduct F H).of_iso
    (hP'.isoIsPullback _ _ hmodel) eA eB eX
    (hP'.isoIsPullback_hom_fst _ _ hmodel).symm (hP'.isoIsPullback_hom_snd _ _ hmodel).symm
    (recognitionMap_localized_square f).symm (recognitionMap_localized_square g).symm

/-- Over an arbitrary localized base, a pullback with Hausdorff factors and
a quasi-étale leg is Hausdorff and has compact preimages of compatible
compact sets of factor pairs. -/
theorem hasCompactPairPreimages_of_quasiEtale
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    [T2Space (localizedSpaceFunctor.obj A)] [T2Space (localizedSpaceFunctor.obj B)]
    (hP : IsPullback p q f g) (hf : quasiEtale f) :
    HasCompactPairPreimages p q f g := by
  obtain ⟨A₀, X₀, f₀, hf₀, ⟨e⟩⟩ := hf
  let eA : localizationFunctor.obj (ofSaturation A₀) ≅ A := Arrow.leftFunc.mapIso e
  let eX : localizationFunctor.obj (ofSaturation X₀) ≅ X := Arrow.rightFunc.mapIso e
  obtain ⟨B₀, hB₀⟩ := localizedObjectEquiv.surjective B
  change localizationFunctor.obj B₀ = B at hB₀
  subst B
  obtain ⟨φ, hφ⟩ := exists_localizedRightFraction (g ≫ eX.inv)
  let eB := localizedQuasiIso φ.s φ.hs
  let p₀ := p ≫ eA.inv
  let q₀ := q ≫ eB.inv
  let : T2Space A₀.space :=
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eA.symm)).t2Space
  let : T2Space φ.X'.presentation.space :=
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eB.symm)).t2Space
  have hf' : f ≫ eX.inv = eA.inv ≫ localizationFunctor.map f₀ := by
    apply (cancel_epi eA.hom).1
    have hw : eA.hom ≫ f = localizationFunctor.map f₀ ≫ eX.hom := e.hom.w
    rw [← Category.assoc, hw, Category.assoc]
    simp
  have hg' : g ≫ eX.inv = eB.inv ≫ localizationFunctor.map φ.f := by
    apply (cancel_epi eB.hom).1
    rw [hφ, Iso.hom_inv_id_assoc]
    exact localizationFunctor_map_s_comp_localizedRightFraction φ
  have hP₀ : IsPullback p₀ q₀ (localizationFunctor.map f₀) (localizationFunctor.map φ.f) := by
    apply hP.of_iso (Iso.refl _) eA.symm eB.symm eX.symm
    · simp [p₀]
    · simp [q₀]
    · exact hf'
    · exact hg'
  exact (hasCompactPairPreimages_of_strongQuasiEtale hP₀ hf₀).of_iso
    (Iso.refl P) eA.symm eB.symm eX.symm (Category.id_comp _).symm (Category.id_comp _).symm hf' hg'

end Langlands.Analytic.SaturatedAtlasPresentation
