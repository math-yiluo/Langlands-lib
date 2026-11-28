import Langlands.Geometry.Analytic.EtaleCoverGluing
import Langlands.Geometry.Analytic.EtaleHomSheafStatement
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Geometry.Analytic.EtaleDomainTargetCancellation
import Langlands.Geometry.Analytic.AnalyticImmersion

/-! # Étale monomorphisms are open immersions

Given the sheaf property of morphisms on the small étale site, an étale monomorphism of
analytic spaces is an isomorphism onto its open image. -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An étale monomorphism is an open immersion, given the étale Hom-sheaf property. -/
theorem openImmersion_of_etale_of_mono (hSheaf : EtaleHomSheafStatement.{u, u})
    {S T : LocalizedCategory.{u, u, u} (K := K)} (f : S ⟶ T) (hf : etale f) [Mono f] :
    openImmersion f := by
  let U := Set.range (localizedSpaceFunctor.map f)
  have hU : IsOpen U := (etaleOpenMap K f hf).isOpen_range
  let D := (presentationOf T).openDomain U hU
  have hmem : ∀ s, localizedSpaceFunctor.map f s ∈ D.carrier := fun s => ⟨s, rfl⟩
  let f' := domainLift D f hmem
  have hf' : f' ≫ domainι T D = f := domainLift_comp D f hmem
  have he : etale f' := etale_of_comp_domainι D (hf'.symm ▸ hf)
  have hmono : Mono f' := mono_of_mono_fac hf'
  have hcov : ∀ t : localizedSpaceFunctor.obj (domainObj T D),
      ∃ _ : PUnit.{u + 1}, t ∈ Set.range (localizedSpaceFunctor.map f') := by
    intro t
    obtain ⟨s, hs⟩ := t.property
    refine ⟨PUnit.unit, s, ?_⟩
    apply Subtype.ext
    rw [val_domainLift_apply]
    exact hs
  have hS := hSheaf K (domainObj T D) S
  obtain ⟨g, hg⟩ := exists_glue_of_etale_cover hS (fun _ : PUnit.{u + 1} => S) (fun _ => f')
    (fun _ => he) hcov (fun _ => 𝟙 S) (fun V _ _ a b hab => by
      rw [Category.comp_id, Category.comp_id]
      exact (cancel_mono f').1 hab)
  have hfg : f' ≫ g = 𝟙 S := hg PUnit.unit
  have hT := hSheaf K (domainObj T D) (domainObj T D)
  have hgf : g ≫ f' = 𝟙 _ := hom_ext_of_etale_cover hT (fun _ : PUnit.{u + 1} => S)
    (fun _ => f') (fun _ => he) hcov _ _ (fun _ => by
      rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id])
  exact ⟨U, hU, ⟨f', g, hfg, hgf⟩, hf'⟩

end Langlands.Analytic.SaturatedAtlasPresentation
