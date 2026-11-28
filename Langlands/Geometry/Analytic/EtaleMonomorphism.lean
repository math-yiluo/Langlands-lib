import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Geometry.Analytic.EtaleTargetDomain
import Langlands.Geometry.Analytic.FiniteAffinoidMonomorphism
import Langlands.Geometry.Analytic.FiniteEtaleOverRecognition
import Langlands.Geometry.Analytic.FullRecognitionChartMorphisms

/-! # Étale monomorphisms and their open images -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Set Filter
open AffinoidAtlasPresentation AffinoidAtlasPresentation.StrongHom
open IndexedAffinoidAtlas PresentedAffinoidAlgebra
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Strong

variable {A B : AffinoidAtlasPresentation.{u, v, v} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)

attribute [local instance] recognizedChartSpectrum_small

set_option backward.isDefEq.respectTransparency false in
private theorem exists_chart_lift [Mono g.fullRecognitionLocalizedHom]
    {V : Set A.space} {U : Set B.space} (hVU : g.IsFiniteEtaleOver V U)
    (W : B.atlas.saturatedAtlas.RecognizedSubset) (hW : W.locus ⊆ U ∩ g.baseMap '' V) :
    ∃ l : localizationFunctor.obj ((ofFullRecognition B).smallChartSpectrum W) ⟶
        localizationFunctor.obj (ofFullRecognition A),
      l ≫ g.fullRecognitionLocalizedHom = (ofFullRecognition B).localizedSmallChart W := by
  obtain ⟨P, hPW, hP, hfin, het⟩ := hVU.2 W (hW.trans inter_subset_left)
  let f : BoundedAlgHom K W.algebra P.algebra := g.fullRecognitionPairs.pullback P W hPW
  let a := SmallAffinoidSpectrum.localizedMapEquiv.{u, v} W.algebra P.algebra f
  let jP := (ofFullRecognition A).localizedSmallChart P
  let jW := (ofFullRecognition B).localizedSmallChart W
  have hw : jP ≫ g.fullRecognitionLocalizedHom = a ≫ jW :=
    localizedSmallChart_comp_fullRecognition g P W hPW
  let : Mono a := by
    constructor
    intro T p q hpq
    have : Mono (a ≫ jW) := hw ▸ (inferInstance : Mono (jP ≫ g.fullRecognitionLocalizedHom))
    apply (cancel_mono (a ≫ jW)).mp
    rw [← Category.assoc, ← Category.assoc, hpq]
  have hs : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom) := by
    intro t
    have ht : W.chart t ∈ W.locus := W.range_chart ▸ mem_range_self t
    obtain ⟨x, hx, hxt⟩ := (hW ht).2
    have hxP : x ∈ P.locus := by
      rw [hP]
      refine ⟨hx, ?_⟩
      change g.baseMap x ∈ W.locus
      rwa [hxt]
    obtain ⟨s, hs⟩ : x ∈ range P.chart := P.range_chart.symm ▸ hxP
    refine ⟨s, W.isEmbedding_chart.injective ?_⟩
    exact (g.fullRecognitionPairs.chart_comm P W hPW s).trans
      ((congrArg g.baseMap hs).trans hxt)
  have hflat := ((BoundedAlgHom.algebraicallyFiniteEtale_iff f).mp het).2.1
  let e := SmallAffinoidSpectrum.isoOfFiniteBanachMonoOfFlatOfSpectrumSurjective.{u, v}
    f hfin hflat hs
  refine ⟨e.inv ≫ jP, ?_⟩
  rw [Category.assoc, hw, ← Category.assoc]
  change (e.inv ≫ e.hom) ≫ jW = jW
  rw [e.inv_hom_id, Category.id_comp]

private theorem isIso_fullRecognition_of_surjective [Mono g.fullRecognitionLocalizedHom]
    (hg : g.IsEtaleAllPieces) (hs : Function.Surjective g.baseMap) :
    IsIso g.fullRecognitionLocalizedHom := by
  let S := ofFullRecognition A
  let T := ofFullRecognition B
  let f := g.fullRecognitionLocalizedHom
  let J : Set T.presentation.atlas.Index :=
    {j | ∃ l : localizationFunctor.obj (T.smallChartSpectrum j) ⟶ localizationFunctor.obj S,
      l ≫ f = T.localizedSmallChart j}
  have hJ : AtlasTopology.LocallyRefines
      (range fun j : J => range (T.presentation.atlas.chart j.val)) {univ} := by
    rintro E hE y -
    obtain rfl := mem_singleton_iff.mp hE
    obtain ⟨x, hxy⟩ := hs y
    obtain ⟨V, U, hV, hU, hxV, hVU⟩ := strongEtaleLocallyFiniteEtale A B g hg x
    have hyV : y ∈ g.baseMap '' V := ⟨x, hxV, hxy⟩
    obtain ⟨I, hIf, hI, hIn⟩ := B.atlas.exists_finite_recognized_nhds_subset y _
      ((hU.inter (hg.isOpenMap _ hV)).mem_nhds ⟨hVU.1 hyV, hyV⟩)
    refine ⟨(fun W => W.locus) '' I, hIf.image _, ?_, ?_, ?_⟩
    · rintro _ ⟨W, hWI, rfl⟩
      exact ⟨⟨W, exists_chart_lift g hVU W (hI W hWI).2⟩, W.range_chart⟩
    · rintro _ ⟨W, hWI, rfl⟩
      exact ⟨subset_univ _, (hI W hWI).1⟩
    · rw [nhdsWithin_univ]
      change ⋃₀ ((fun W : B.atlas.saturatedAtlas.RecognizedSubset => W.locus) '' I) ∈
        𝓝 (show B.space from y)
      rw [sUnion_image]
      exact hIn
  obtain ⟨l, hl, -⟩ := exists_lift_of_chartCover (A := T) (fun j : J => j.val) hJ f f
    (fun _ _ _ h _ => (cancel_mono f).mp h) (𝟙 _) (𝟙 _) (fun j => by
      obtain ⟨b, hb⟩ := j.property
      exact ⟨b, hb.trans (Category.comp_id _).symm, hb.trans (Category.comp_id _).symm⟩)
  refine ⟨⟨l, (cancel_mono f).mp ?_, hl⟩⟩
  rw [Category.assoc, hl, Category.comp_id, Category.id_comp]

end Strong

section Localized

variable {X Y : LocalizedCategory.{u, v, v} (K := K)}

set_option backward.isDefEq.respectTransparency false in
/-- An étale monomorphism that is surjective on points is an isomorphism. -/
theorem isIso_of_etale_mono_of_surjective (f : X ⟶ Y) [Mono f] (hf : etale f)
    (hs : Function.Surjective (localizedSpaceFunctor.map f)) : IsIso f := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let a := Arrow.leftFunc.mapIso e
  let b := Arrow.rightFunc.mapIso e
  have hg_eq : localizationFunctor.map g = a.hom ≫ f ≫ b.inv := Arrow.iso_w' e.symm
  have hfull : g.fullRecognitionLocalizedHom =
      (fullRecognitionIso A).inv ≫ localizationFunctor.map g ≫ (fullRecognitionIso B).hom := by
    rw [← fullRecognitionIso_naturality g, Iso.inv_hom_id_assoc]
  let : Mono g.fullRecognitionLocalizedHom := by
    rw [hfull, hg_eq]
    infer_instance
  have hgs : Function.Surjective g.baseMap := by
    change Function.Surjective (localizedSpaceFunctor.map (localizationFunctor.map g))
    rw [hg_eq, Functor.map_comp, Functor.map_comp, TopCat.coe_comp, TopCat.coe_comp]
    exact (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso b.symm)).surjective.comp
      (hs.comp (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso a)).surjective)
  let : IsIso g.fullRecognitionLocalizedHom := isIso_fullRecognition_of_surjective g hg hgs
  have hg_full : localizationFunctor.map g =
      (fullRecognitionIso A).hom ≫ g.fullRecognitionLocalizedHom ≫ (fullRecognitionIso B).inv := by
    rw [← Category.assoc, fullRecognitionIso_naturality g, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  let : IsIso (localizationFunctor.map g) := by
    rw [hg_full]
    infer_instance
  rw [Arrow.iso_w' e]
  infer_instance

/-- The open analytic domain given by the range of an étale morphism. -/
def etaleImageDomain (f : X ⟶ Y) (hf : etale f) : (presentationOf Y).AnalyticDomain :=
  (presentationOf Y).openDomain (range (localizedSpaceFunctor.map f))
    (etaleOpenMap K f hf).isOpen_range

set_option backward.isDefEq.respectTransparency false in
/-- An étale monomorphism is isomorphic to the open analytic domain of its image. -/
def etaleMonoImageIso (f : X ⟶ Y) [Mono f] (hf : etale f) :
    X ≅ domainObj Y (etaleImageDomain f hf) := by
  let D := etaleImageDomain f hf
  let hD : ∀ x, localizedSpaceFunctor.map f x ∈ D.carrier := fun x => mem_range_self x
  let g := domainLift D f hD
  have hgf : g ≫ domainι Y D = f := domainLift_comp D f hD
  let : Mono g := by
    constructor
    intro T a b hab
    apply (cancel_mono f).mp
    rw [← hgf, ← Category.assoc, ← Category.assoc, hab]
  have hg : etale g := etaleTargetDomain D g (hgf.symm ▸ hf)
  have hgs : Function.Surjective (localizedSpaceFunctor.map g) := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    exact ⟨x, Subtype.ext ((val_domainLift_apply D f hD x).trans hx)⟩
  let : IsIso g := isIso_of_etale_mono_of_surjective g hg hgs
  exact asIso g

@[reassoc (attr := simp)]
theorem etaleMonoImageIso_hom_comp_domainι (f : X ⟶ Y) [Mono f] (hf : etale f) :
    (etaleMonoImageIso f hf).hom ≫ domainι Y (etaleImageDomain f hf) = f :=
  domainLift_comp (etaleImageDomain f hf) f (fun x => mem_range_self x)

theorem openImmersion_of_etale_mono (f : X ⟶ Y) [Mono f] (hf : etale f) :
    openImmersion f :=
  ⟨_, _, etaleMonoImageIso f hf, etaleMonoImageIso_hom_comp_domainι f hf⟩

end Localized

end Langlands.Analytic.SaturatedAtlasPresentation
