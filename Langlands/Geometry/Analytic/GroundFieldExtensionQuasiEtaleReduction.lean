import Langlands.Geometry.Analytic.GroundFieldExtensionDomainEmbeddings
import Langlands.Geometry.Analytic.LocalizedQuasiEtaleLocality

/-! # Quasi-étale factorizations under ground field extension -/

noncomputable section

universe u u' v

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open _root_.CategoryTheory Set Filter Topology SaturatedAtlasPresentation

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

local notation "F" => localizedFunctor K L

/-- Preservation of localized étale maps by ground field extension suffices
for preservation of localized quasi-étale maps by the same functor. -/
theorem quasiEtale_scalarExtension_of_preservesEtale
    (he : ∀ {Y X : LocalizedCategory.{u, v, v} (K := K)} (f : Y ⟶ X), etale f → etale ((F).map f))
    {Y X : LocalizedCategory.{u, v, v} (K := K)} (f : Y ⟶ X) (hf : quasiEtale f) :
    quasiEtale ((F).map f) := by
  revert f
  obtain ⟨SA, rfl⟩ := localizedObjectEquiv.surjective Y
  intro f
  change localizationFunctor.obj SA ⟶ X at f
  intro hf
  let AL := IndexedAffinoidAtlas.GroundFieldExtension.presentation K L SA.presentation.atlas
  let ψ : localizationFunctor.obj (ofSaturation AL) ⟶ (F).obj X := (F).map f
  change quasiEtale ψ
  apply quasiEtale_of_forall_isLocalizedQuasiEtaleAt (S := ofSaturation AL)
  intro y
  let p := IndexedAffinoidAtlas.GroundFieldExtension.projection K L SA.presentation.atlas
  have hp : Continuous p := IndexedAffinoidAtlas.GroundFieldExtension.continuous_projection K L SA.presentation.atlas
  obtain ⟨σ, hσ, hn, hpiece⟩ := isLocalizedQuasiEtaleAt_of_quasiEtale (S := SA) hf (p y)
  refine ⟨(Set.preimage p) '' σ, hσ.image _, ?_, ?_⟩
  · refine Filter.mem_of_superset (hp.continuousAt.preimage_mem_nhds hn) ?_
    intro z hz
    obtain ⟨V, hV, hzV⟩ := mem_sUnion.mp (show p z ∈ ⋃₀ σ from hz)
    exact mem_sUnion.mpr ⟨_, ⟨V, hV, rfl⟩, hzV⟩
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨i, hi, W, w, j, hw, hj, htri⟩ := hpiece V hV
    let k := extendedChartIndex K L SA i
    have hchart : range ((ofSaturation AL).presentation.atlas.chart k) = p ⁻¹' V := by
      let a := IndexedAffinoidAtlas.GroundFieldExtension.atlas K L SA.presentation.atlas
      refine (a.saturatedAtlas_original_range i).trans ?_
      exact (IndexedAffinoidAtlas.GroundFieldExtension.range_chart K L SA.presentation.atlas i).trans
        (congrArg (Set.preimage p) hi)
    let e := extendedChartDomainIso K L SA i
    refine ⟨k, hchart, (F).obj W, (F).map w, e.inv ≫ (F).map j, he w hw,
      (isAffinoidDomainEmbedding_localizedFunctor_map K L hj).iso_comp e.symm, ?_⟩
    rw [Category.assoc, ← Functor.map_comp, htri, Functor.map_comp]
    rw [← extendedChartDomainIso_hom_inclusion K L SA i]
    change e.inv ≫ (e.hom ≫ (ofSaturation AL).localizedDomainInclusion
      ((ofSaturation AL).chartDomain k)) ≫ ψ =
      (ofSaturation AL).localizedDomainInclusion ((ofSaturation AL).chartDomain k) ≫ ψ
    exact (Category.assoc e.inv _ ψ).symm.trans
      (congrArg (· ≫ ψ) (Iso.inv_hom_id_assoc e _))

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
