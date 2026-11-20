import Langlands.Geometry.Analytic.FiniteEtaleCoverRefinements
import Langlands.Geometry.Analytic.FiniteAffinoidLocalizedHomDescent
import Langlands.Geometry.Analytic.FullRecognitionPairComposition
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.RecognizedContainedMap

/-! # Detection of analytic morphisms along étale covers -/

noncomputable section

universe u v i

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas
open AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem fullRecognition_pullback_congr
    {A C : AffinoidAtlasPresentation.{u, v, v} K} {f g : ofSaturation A ⟶ ofSaturation C}
    (h : f = g) (P : A.atlas.saturatedAtlas.RecognizedSubset)
    (Z : C.atlas.saturatedAtlas.RecognizedSubset)
    (hf : f.baseMap '' range P.chart ⊆ range Z.chart)
    (hg : g.baseMap '' range P.chart ⊆ range Z.chart) :
    f.fullRecognitionPairs.pullback P Z hf = g.fullRecognitionPairs.pullback P Z hg := by
  subst g
  rfl

/-- Agreement after a jointly surjective family of strong étale maps
implies equality of complete strong maps. -/
theorem strongHom_ext_of_etale_family {ι : Type i}
    {B C : AffinoidAtlasPresentation.{u, v, v} K}
    {A : ι → AffinoidAtlasPresentation.{u, v, v} K}
    (e : ∀ b, ofSaturation (A b) ⟶ ofSaturation B)
    (he : ∀ b, (e b).IsEtaleAllPieces)
    (hcov : ∀ y : B.space, ∃ b z, (e b).baseMap z = y)
    (f g : ofSaturation B ⟶ ofSaturation C)
    (heq : ∀ b, e b ≫ f = e b ≫ g) : f = g := by
  have hbase : f.baseMap = g.baseMap := by
    ext y
    obtain ⟨b, z, rfl⟩ := hcov y
    exact congrArg (fun k : ofSaturation (A b) ⟶ ofSaturation C => k.baseMap z) (heq b)
  refine ext_of_saturated B.atlas.saturatedAtlas_hasAllLocalDomains hbase ?_
  intro j
  obtain ⟨l, hf⟩ := f.target_exists j
  have hg : g.baseMap '' range (B.atlas.saturatedAtlas.chart j) ⊆
      range (C.atlas.saturatedAtlas.chart l) := hbase ▸ hf
  refine ⟨l, hf, ?_⟩
  obtain ⟨n, b, k, P, h, hsub, hcover, hfinite⟩ :=
    strongEtaleFiniteChartRefinement B A e he hcov j
  let W := fun t => B.atlas.saturatedAtlas.originalRecognitionIndex (k t)
  let Z := C.atlas.saturatedAtlas.originalRecognitionIndex l
  have hZ : Z.locus ⊆ range (C.atlas.saturatedAtlas.chart l) := Subset.rfl
  let cov : Domain.FiniteCover (Domain.whole K (B.atlas.saturatedAtlas.algebra j)) := {
    size := n
    obj t := (W t).containedDomain j (hsub t)
    map t := ⟨(W t).containedRestriction j (hsub t), BoundedAlgHom.comp_id _⟩
    covers x _ := by
      obtain ⟨t, ht⟩ := mem_iUnion.mp (hcover (mem_range_self x))
      exact ⟨t, ht⟩ }
  apply BoundedAlgHom.ext
  intro r
  apply cov.algebra_ext_of_restrict_eq
  intro t
  let F := (e (b t)).fullRecognitionPairs.pullback (P t) (W t) (h t)
  obtain ⟨_, hEt, hsurj⟩ := hfinite t
  have hflat := (BoundedAlgHom.algebraicallyFiniteEtale_iff F).mp hEt |>.2.1
  have hfinj : Function.Injective F := by
    let : Algebra (W t).algebra (P t).algebra := F.toAlgHom.toRingHom.toAlgebra
    have : Module.FaithfullyFlat (W t).algebra (P t).algebra :=
      SmallAffinoidSpectrum.faithfullyFlat_of_flat_of_spectrum_surjective F hflat hsurj
    exact FaithfulSMul.algebraMap_injective (W t).algebra (P t).algebra
  have hWr : range (W t).chart ⊆ range (B.atlas.saturatedAtlas.chart j) :=
    (W t).range_chart.subset.trans (hsub t)
  have hWf : f.baseMap '' range (W t).chart ⊆ range Z.chart :=
    (image_mono hWr).trans (hf.trans Z.range_chart.symm.subset)
  have hWg : g.baseMap '' range (W t).chart ⊆ range Z.chart := hbase ▸ hWf
  have hPf : (e (b t) ≫ f).baseMap '' range (P t).chart ⊆ range Z.chart := by
    rintro _ ⟨x, hx, rfl⟩
    exact hWf ⟨_, h t ⟨x, hx, rfl⟩, rfl⟩
  have hPg : (e (b t) ≫ g).baseMap '' range (P t).chart ⊆ range Z.chart :=
    (heq (b t)) ▸ hPf
  have hcomp : F.comp (f.fullRecognitionPairs.pullback (W t) Z hWf) =
      F.comp (g.fullRecognitionPairs.pullback (W t) Z hWg) :=
    (fullRecognitionPairs_comp (e (b t)) f (P t) (W t) Z (h t) hWf hPf).symm.trans
      ((fullRecognition_pullback_congr (heq (b t)) (P t) Z hPf hPg).trans
        (fullRecognitionPairs_comp (e (b t)) g (P t) (W t) Z (h t) hWg hPg))
  have hW : f.fullRecognitionPairs.pullback (W t) Z hWf =
      g.fullRecognitionPairs.pullback (W t) Z hWg :=
    BoundedAlgHom.ext fun a => hfinj (congrArg (fun q => q a) hcomp)
  have hFc := f.fullRecognitionPairs_comp_containedRestriction
    (W t) Z j l (hsub t) hZ hf hWf
  have hGc := g.fullRecognitionPairs_comp_containedRestriction
    (W t) Z j l (hsub t) hZ hg hWg
  have h := hFc.symm.trans
    ((congrArg (fun q => q.comp (Z.containedRestriction l hZ)) hW).trans hGc)
  exact congrArg (fun q => q r) h

/-- An étale arrow whose target is a constructed saturation has a strong
étale representative with that exact target, after a source isomorphism. -/
theorem exists_strongEtale_representative
    {X : LocalizedCategory.{u, v, v} (K := K)} {B : AffinoidAtlasPresentation.{u, v, v} K}
    (e : X ⟶ localizationFunctor.obj (ofSaturation B)) (he : etale e) :
    ∃ (A : AffinoidAtlasPresentation.{u, v, v} K)
      (m : ofSaturation A ⟶ ofSaturation B) (r : localizationFunctor.obj (ofSaturation A) ≅ X),
      m.IsEtaleAllPieces ∧ r.hom ≫ e = localizationFunctor.map m := by
  obtain ⟨X₀, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction e
  let r := localizationFunctor.mapIso φ.X'.saturationIso ≪≫ localizedQuasiIso φ.s φ.hs
  let m := φ.X'.saturationIso.hom ≫ φ.f
  have hm : r.hom ≫ localizedRightFraction φ = localizationFunctor.map m := by
    change (localizationFunctor.map φ.X'.saturationIso.hom ≫ localizationFunctor.map φ.s) ≫
      localizedRightFraction φ = localizationFunctor.map m
    rw [Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction, Functor.map_comp]
  exact ⟨_, m, r, (etale_localizationFunctor_map_ofSaturation_iff m).mp
    (hm ▸ etale_comp (etale_of_isIso r.hom) he), hm⟩

/-- Equality of complete localized analytic maps is local for jointly
surjective families of étale arrows. -/
def EtaleCoverHomExtStatement : Prop :=
  ∀ {ι : Type i} {X T : LocalizedCategory.{u, v, v} (K := K)}
    {U : ι → LocalizedCategory.{u, v, v} (K := K)} (e : ∀ b, U b ⟶ X),
    (∀ b, etale (e b)) →
    (∀ x : localizedSpaceFunctor.obj X, ∃ b, x ∈ Set.range (localizedSpaceFunctor.map (e b))) →
    ∀ (f g : X ⟶ T), (∀ b, e b ≫ f = e b ≫ g) → f = g

theorem etaleCoverHomExt : EtaleCoverHomExtStatement.{u, v, i} (K := K) := by
  intro ι X T U e he hcov f g heq
  obtain ⟨X₀, hX⟩ := localizedObjectEquiv.surjective X
  obtain ⟨T₀, hT⟩ := localizedObjectEquiv.surjective T
  change localizationFunctor.obj X₀ = X at hX
  change localizationFunctor.obj T₀ = T at hT
  subst X T
  obtain ⟨S, s, hs, F, G, hF, hG⟩ := exists_commonStrongNumerators f g
  let xIso := localizationFunctor.mapIso S.saturationIso ≪≫ localizedQuasiIso s hs
  let tIso := localizationFunctor.mapIso T₀.saturationIso
  let F' := S.saturationIso.hom ≫ F ≫ T₀.saturationIso.inv
  let G' := S.saturationIso.hom ≫ G ≫ T₀.saturationIso.inv
  have hcompare (p : localizationFunctor.obj X₀ ⟶ localizationFunctor.obj T₀)
      (P : S ⟶ T₀) (hp : localizationFunctor.map s ≫ p = localizationFunctor.map P) :
      xIso.hom ≫ p =
        localizationFunctor.map (S.saturationIso.hom ≫ P ≫ T₀.saturationIso.inv) ≫
          tIso.hom := by
    change (localizationFunctor.map S.saturationIso.hom ≫ localizationFunctor.map s) ≫ p =
      localizationFunctor.map (S.saturationIso.hom ≫ P ≫ T₀.saturationIso.inv) ≫
        localizationFunctor.map T₀.saturationIso.hom
    rw [Category.assoc, hp, ← Functor.map_comp, ← Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hF' : xIso.hom ≫ f = localizationFunctor.map F' ≫ tIso.hom := hcompare f F hF
  have hG' : xIso.hom ≫ g = localizationFunctor.map G' ≫ tIso.hom := hcompare g G hG
  let e' := fun b => e b ≫ xIso.inv
  choose A E r hE hr using fun b => exists_strongEtale_representative (e' b)
    (etale_comp (he b) (etale_of_isIso xIso.inv))
  have hr' (b : ι) : localizationFunctor.map (E b) ≫ xIso.hom = (r b).hom ≫ e b := by
    rw [← hr b]
    change ((r b).hom ≫ (e b ≫ xIso.inv)) ≫ xIso.hom = (r b).hom ≫ e b
    rw [Category.assoc (r b).hom, Category.assoc (e b), Iso.inv_hom_id, Category.comp_id]
  have hstrongCov (x : S.presentation.space) : ∃ b z, (E b).baseMap z = x := by
    obtain ⟨b, z, hz⟩ := hcov (localizedSpaceFunctor.map xIso.hom x)
    let z' := localizedSpaceFunctor.map (r b).inv z
    refine ⟨b, z', (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso xIso)).injective ?_⟩
    have hz' : localizedSpaceFunctor.map (r b).hom z' = z := by
      exact congrArg (fun p : localizedSpaceFunctor.obj (U b) ⟶ _ => p z)
        (localizedSpaceFunctor.mapIso (r b)).inv_hom_id
    change localizedSpaceFunctor.map xIso.hom ((E b).baseMap z') =
      localizedSpaceFunctor.map xIso.hom x
    calc
      _ = localizedSpaceFunctor.map (localizationFunctor.map (E b) ≫ xIso.hom) z' := by
        rw [Functor.map_comp, TopCat.comp_app, localizedSpaceFunctor_map]
        rfl
      _ = localizedSpaceFunctor.map ((r b).hom ≫ e b) z' :=
        congrArg (fun p : localizationFunctor.obj (ofSaturation (A b)) ⟶
          localizationFunctor.obj X₀ => localizedSpaceFunctor.map p z') (hr' b)
      _ = _ := by rw [Functor.map_comp, TopCat.comp_app, hz', hz]
  have hstrongEq (b : ι) : E b ≫ F' = E b ≫ G' := by
    have hcomp (p : localizationFunctor.obj X₀ ⟶ localizationFunctor.obj T₀)
        (P : ofSaturation S.presentation ⟶ ofSaturation T₀.presentation)
        (hp : xIso.hom ≫ p = localizationFunctor.map P ≫ tIso.hom) :
        localizationFunctor.map (E b ≫ P) ≫ tIso.hom = (r b).hom ≫ (e b ≫ p) := by
      rw [Functor.map_comp, Category.assoc, ← hp,
        ← Category.assoc (localizationFunctor.map (E b)), hr' b, Category.assoc]
    apply localizationFunctor_map_injective
    apply (cancel_mono tIso.hom).mp
    exact (hcomp f F' hF').trans
      ((congrArg ((r b).hom ≫ ·) (heq b)).trans (hcomp g G' hG').symm)
  have hfg := strongHom_ext_of_etale_family E hE hstrongCov F' G' hstrongEq
  apply (cancel_epi xIso.hom).mp
  exact hF'.trans ((congrArg (fun p => localizationFunctor.map p ≫ tIso.hom) hfg).trans hG'.symm)

end Langlands.Analytic.SaturatedAtlasPresentation
