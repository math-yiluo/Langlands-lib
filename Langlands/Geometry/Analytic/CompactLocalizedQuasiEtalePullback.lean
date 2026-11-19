import Langlands.Geometry.Analytic.CompactSmallFibreProduct
import Langlands.Geometry.Analytic.LocalizedQuasiEtalePullbackExistence

/-! # Compactness of localized pullbacks along quasi-étale morphisms -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem isCompactSpace_of_strong_quasiEtale_pullback
    {A X : AffinoidAtlasPresentation.{u, v, v} K}
    {B : SaturatedAtlasPresentation.{u, v, v} K}
    {P : LocalizedCategory.{u, v, v} (K := K)}
    {f : ofSaturation A ⟶ ofSaturation X} {g : B ⟶ ofSaturation X}
    {p : P ⟶ localizationFunctor.obj (ofSaturation A)} {q : P ⟶ localizationFunctor.obj B}
    (hP : IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g))
    (hf : IsQuasiEtale f) (hA : IsCompactSpace (localizationFunctor.obj (ofSaturation A)))
    (hB : IsCompactSpace (localizationFunctor.obj B))
    (hX : T2Space (localizedSpaceFunctor.obj (localizationFunctor.obj (ofSaturation X)))) :
    IsCompactSpace P := by
  let F := recognitionMap f
  let G := recognitionMap g
  let : Small.{v} (FibreProduct.chartSystem
      (geometricCompatibleMap F) (geometricCompatibleMap G)).Space :=
    small_recognition_fibreProductSpace_of_domainEtaleCharts f g (by
      intro y
      obtain ⟨σ, _, hn, hs⟩ := hf.exists_local_domainEtale_charts y
      obtain ⟨V, hV, hyV⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hn)
      obtain ⟨i, hi, hfactor⟩ := hs V hV
      exact ⟨i, hi.symm ▸ hyV,
        by simpa only [Functor.map_comp, localizedDomainInclusion] using hfactor⟩)
  have hA' := hA.of_iso (recognitionSourceIso f)
  have hB' := hB.of_iso (recognitionSourceIso g)
  let : CompactSpace (recognitionSource f).presentation.space := hA'.1
  let : CompactSpace (recognitionSource g).presentation.space := hB'.1
  let : T2Space (recognitionSource f).presentation.space := hA'.2
  let : T2Space (recognitionSource g).presentation.space := hB'.2
  let : T2Space (recognitionBase (ofSaturation X)).presentation.space :=
    haveI := hX
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso
      (recognitionBaseIso (ofSaturation X)))).t2Space
  let p' := p ≫ (recognitionSourceIso f).hom
  let q' := q ≫ (recognitionSourceIso g).hom
  have hP' : IsPullback p' q' (localizationFunctor.map F) (localizationFunctor.map G) := by
    apply hP.of_iso (Iso.refl _) (recognitionSourceIso f) (recognitionSourceIso g)
      (recognitionBaseIso (ofSaturation X))
    · simp [p']
    · simp [q']
    · exact (recognitionMap_localized_square f).symm
    · exact (recognitionMap_localized_square g).symm
  exact (isCompactSpace_localization_smallFibreProduct F G).of_iso
    ((smallFibreProduct_isPullback F G).isoIsPullback _ _ hP')

/-- Every localized pullback along a quasi-étale first leg is compact
Hausdorff when both factors are compact Hausdorff and the base is Hausdorff. -/
theorem isCompactSpace_of_isPullback_of_quasiEtale
    {A B X P : LocalizedCategory.{u, v, v} (K := K)}
    {f : A ⟶ X} {g : B ⟶ X} {p : P ⟶ A} {q : P ⟶ B}
    (hP : IsPullback p q f g) (hf : quasiEtale f)
    (hA : IsCompactSpace A) (hB : IsCompactSpace B)
    (hX : T2Space (localizedSpaceFunctor.obj X)) : IsCompactSpace P := by
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
  have hP₀ : IsPullback p₀ q₀ (localizationFunctor.map f₀) (localizationFunctor.map φ.f) := by
    apply hP.of_iso (Iso.refl _) eA.symm eB.symm eX.symm
    · simp [p₀]
    · simp [q₀]
    · change f ≫ eX.inv = eA.inv ≫ localizationFunctor.map f₀
      apply (cancel_epi eA.hom).1
      have hw : eA.hom ≫ f = localizationFunctor.map f₀ ≫ eX.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc]
      simp
    · change g ≫ eX.inv = eB.inv ≫ localizationFunctor.map φ.f
      apply (cancel_epi eB.hom).1
      rw [hφ, Iso.hom_inv_id_assoc]
      exact localizationFunctor_map_s_comp_localizedRightFraction φ
  have hX₀ : T2Space (localizedSpaceFunctor.obj (localizationFunctor.obj (ofSaturation X₀))) :=
    haveI := hX
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eX.symm)).t2Space
  exact isCompactSpace_of_strong_quasiEtale_pullback hP₀ hf₀
    (hA.of_iso eA.symm) (hB.of_iso eB.symm) hX₀

/-- The chosen full localized pullback along a quasi-étale first leg, with
the compact Hausdorff property of its point. -/
def compactLocalizedQuasiEtalePullback
    {A B X : LocalizedCategory.{u, v, v} (K := K)} (f : A ⟶ X) (g : B ⟶ X)
    (hf : quasiEtale f) (hA : IsCompactSpace A) (hB : IsCompactSpace B)
    (hX : T2Space (localizedSpaceFunctor.obj X)) : CompactLocalizedPullbackData f g :=
  let c := localizedQuasiEtalePullback f g hf
  ⟨c.1, c.2, isCompactSpace_of_isPullback_of_quasiEtale
    (IsPullback.of_isLimit c.2) hf hA hB hX⟩

end Langlands.Analytic.SaturatedAtlasPresentation
