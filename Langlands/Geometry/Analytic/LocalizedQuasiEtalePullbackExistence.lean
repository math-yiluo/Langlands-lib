import Langlands.Geometry.Analytic.QuasiEtaleDomainChartCover
import Langlands.Geometry.Analytic.QuasiEtalePullbackSmallness
import Langlands.Geometry.Analytic.RecognizedLocalizedPullbacks

/-! # Pullback existence along localized quasi-étale morphisms -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem exists_pullback_of_strong_quasiEtale
    {A C : AffinoidAtlasPresentation.{u, v, v} K}
    {B : SaturatedAtlasPresentation.{u, v, v} K}
    (f : ofSaturation A ⟶ ofSaturation C) (g : B ⟶ ofSaturation C)
    (hf : IsQuasiEtale f) :
    ∃ (P : LocalizedCategory.{u, v, v} (K := K))
      (p : P ⟶ localizationFunctor.obj (ofSaturation A)) (q : P ⟶ localizationFunctor.obj B),
      IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g) := by
  let : Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap (recognitionMap f))
      (geometricCompatibleMap (recognitionMap g))).Space :=
    small_recognition_fibreProductSpace_of_domainEtaleCharts f g (by
      intro y
      obtain ⟨σ, _, hσ, hfactor⟩ := hf.exists_local_domainEtale_charts y
      obtain ⟨V, hV, hyV⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hσ)
      obtain ⟨i, hi, hiFactor⟩ := hfactor V hV
      exact ⟨i, hi.symm ▸ hyV, by
        simpa only [Functor.map_comp, localizedDomainInclusion] using hiFactor⟩)
  let F := recognitionMap f
  let G := recognitionMap g
  let p := localizationFunctor.map (smallFibreProductFst F G) ≫ (recognitionSourceIso f).inv
  let q := localizationFunctor.map (smallFibreProductSnd F G) ≫ (recognitionSourceIso g).inv
  refine ⟨_, p, q, ?_⟩
  apply (smallFibreProduct_isPullback F G).of_iso (Iso.refl _)
    (recognitionSourceIso f).symm (recognitionSourceIso g).symm (recognitionBaseIso (ofSaturation C)).symm
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    rfl
  · exact recognitionMap_localized_inverse_square f
  · exact recognitionMap_localized_inverse_square g

/-- Pullbacks along quasi-étale morphisms exist in the full localized
analytic category, in the original space and atlas-index universe. -/
theorem exists_localizedPullback_of_quasiEtale
    {A B X : LocalizedCategory.{u, v, v} (K := K)}
    (f : A ⟶ X) (g : B ⟶ X) (hf : quasiEtale f) :
    ∃ (P : LocalizedCategory.{u, v, v} (K := K)) (p : P ⟶ A) (q : P ⟶ B),
      IsPullback p q f g := by
  obtain ⟨A₀, X₀, f₀, hf₀, ⟨e⟩⟩ := hf
  let eA : localizationFunctor.obj (ofSaturation A₀) ≅ A := Arrow.leftFunc.mapIso e
  let eX : localizationFunctor.obj (ofSaturation X₀) ≅ X := Arrow.rightFunc.mapIso e
  obtain ⟨B₀, hB₀⟩ := localizedObjectEquiv.surjective B
  change localizationFunctor.obj B₀ = B at hB₀
  subst B
  obtain ⟨φ, hφ⟩ := exists_localizedRightFraction (g ≫ eX.inv)
  let eB := localizedQuasiIso φ.s φ.hs
  obtain ⟨P, p, q, hP⟩ := exists_pullback_of_strong_quasiEtale f₀ φ.f hf₀
  refine ⟨P, p ≫ eA.hom, q ≫ eB.hom, ?_⟩
  apply hP.of_iso (Iso.refl _) eA eB eX
  · simp
  · simp
  · exact e.hom.w.symm
  · change localizationFunctor.map φ.f ≫ eX.hom = localizationFunctor.map φ.s ≫ g
    rw [← localizationFunctor_map_s_comp_localizedRightFraction φ, ← hφ]
    simp only [Category.assoc, eX.inv_hom_id, Category.comp_id]

/-- Choose the actual limiting cone for a localized cospan with a
quasi-étale first leg. -/
def localizedQuasiEtalePullback
    {A B X : LocalizedCategory.{u, v, v} (K := K)}
    (f : A ⟶ X) (g : B ⟶ X) (hf : quasiEtale f) :
    Σ c : PullbackCone f g, IsLimit c :=
  Classical.choice (show Nonempty (Σ c : PullbackCone f g, IsLimit c) from by
    obtain ⟨P, p, q, hP⟩ := exists_localizedPullback_of_quasiEtale f g hf
    exact ⟨⟨PullbackCone.mk p q hP.w, hP.isLimit⟩⟩)

end Langlands.Analytic.SaturatedAtlasPresentation
