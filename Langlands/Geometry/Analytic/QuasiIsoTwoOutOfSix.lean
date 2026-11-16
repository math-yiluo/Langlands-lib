import Langlands.Geometry.Analytic.StrongIsoQuasiIso
import Langlands.Geometry.Analytic.QuasiIsoSourceEtale
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization

/-! # Two-out-of-six for full strong quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra

/-- Two consecutive domain composites force the first bounded map to
represent the inverse-image domain. -/
theorem Represents.of_comp_of_comp
    {R S T U : PresentedAffinoidAlgebra K}
    {a : BoundedAlgHom K S T} {b : BoundedAlgHom K R S} {c : BoundedAlgHom K U R}
    {V : Set (BanachSpectrum R)} {W : Set (BanachSpectrum U)}
    (hab : Represents K (a.comp b) V) (hbc : Represents K (b.comp c) W) :
    Represents K a ((BanachSpectrum.comap b.toBoundedRingHom) ⁻¹' V) := by
  let D : Domain K U := ⟨S, b.comp c, W, hbc⟩
  have hinj : Function.Injective (BanachSpectrum.comap b.toBoundedRingHom) := by
    intro x y hxy
    apply D.spectrumMap_injective
    exact congrArg (BanachSpectrum.comap c.toBoundedRingHom) hxy
  have hbepi : ∀ (E : PresentedAffinoidAlgebra K) (α β : BoundedAlgHom K S E),
      α.comp b = β.comp b → α = β := by
    intro E α β heq
    apply hbc.hom_ext E
    exact congrArg (fun m : BoundedAlgHom K R E => m.comp c) heq
  refine ⟨hab.1.preimage (BanachSpectrum.comapContinuous b.toBoundedRingHom).continuous,
    ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hab.hasImageIn y
    · intro hx
      obtain ⟨y, hy⟩ := hab.2.1.symm ▸ hx
      exact ⟨y, hinj hy⟩
  · intro E φ hφ
    have hφb : HasImageIn K (φ.comp b) V := fun x => hφ x
    obtain ⟨ψ, hψ, huniq⟩ := hab.2.2 E (φ.comp b) hφb
    refine ⟨ψ, hbepi E _ _ hψ, ?_⟩
    intro χ hχ
    apply huniq χ
    change (χ.comp a).comp b = φ.comp b
    rw [hχ]

end PresentedAffinoidAlgebra

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Full quasi-isomorphisms cancel from the source of a composite between
constructed saturations. -/
theorem IsQuasiIso.of_saturatedComp_left
    {f : StrongHom A.saturatedPresentation B.saturatedPresentation}
    {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
    (hf : f.IsQuasiIso)
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsQuasiIso) : g.IsQuasiIso := by
  have hh : IsHomeomorph g.baseMap := by
    have he : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap ∘ hf.1.homeomorph.symm =
          g.baseMap := by
      funext y
      exact congrArg g.baseMap (hf.1.homeomorph.apply_symm_apply y)
    exact he ▸ hfg.1.comp hf.1.homeomorph.symm.isHomeomorph
  apply IsomorphismCriterion.isQuasiIso
  refine ⟨hh, fun W => ?_⟩
  let V := hf.originalRestriction.generalReverseRecognizedImage f.originalRestriction.coherent W
  let Z := hfg.fullRecognitionImage V
  let d := hfg.fullRecognitionImageEquiv V
  have hVimage : f.baseMap '' V.locus = W.locus := by
    rw [hf.originalRestriction.generalReverseRecognizedImage_locus]
    exact Set.image_preimage_eq _ hf.1.surjective
  have hVW : f.baseMap '' Set.range V.chart ⊆ Set.range W.chart :=
    (Set.image_mono V.range_chart.subset).trans
      (hVimage.subset.trans W.range_chart.superset)
  have hu : W.chart ⁻¹' (f.baseMap '' V.locus) = Set.univ := by
    exact (congrArg (fun s : Set B.space => W.chart ⁻¹' s) hVimage).trans
      (W.range_chart ▸ Set.preimage_range W.chart)
  let e := hf.fullRecognitionPairEquiv V W hVW hVimage.subset hu
  have hZ : Z.locus = g.baseMap '' W.locus := by
    exact (hfg.fullRecognitionImage_locus V).trans
      ((Set.image_image g.baseMap f.baseMap V.locus).symm.trans
        (congrArg (fun s => g.baseMap '' s) hVimage))
  have hWZ : g.baseMap '' Set.range W.chart ⊆ Set.range Z.chart :=
    (Set.image_mono W.range_chart.subset).trans
      (hZ.symm.subset.trans Z.range_chart.superset)
  have hVZ := hfg.fullRecognitionImage_admissible V
  refine ⟨Z, hWZ, hZ, d.trans e.symm, ?_⟩
  apply BoundedAlgHom.ext
  intro z
  apply e.injective
  change e (e.symm (d z)) = e (g.fullRecognitionPairs.pullback W Z hWZ z)
  rw [e.apply_symm_apply]
  exact congrArg (fun m => m z) (fullRecognitionPairs_comp f g V W Z hVW hWZ hVZ)

end AffinoidAtlasPresentation.StrongHom
namespace SaturatedAtlasPresentation

variable {A B C D : SaturatedAtlasPresentation.{u, v, w} K}

/-- Full source cancellation for actual saturated-category compositions. -/
theorem isQuasiIso_of_comp_left {f : A ⟶ B} {g : B ⟶ C}
    (hf : f.IsQuasiIso) (hfg : (f ≫ g).IsQuasiIso) : g.IsQuasiIso := by
  let F := compatibleFunctor (K := K) ⋙ CompatibleAtlasPresentation.saturationFunctor
  have hcomp : (F.map f ≫ F.map g).IsQuasiIso :=
    (congrArg (fun m => m.IsQuasiIso) (F.map_comp f g)).mp
      (hfg.saturationExtension
        ((f ≫ g).hasCoherentPullbacks_of_saturated A.hasAllLocalDomains))
  have hg := AffinoidAtlasPresentation.StrongHom.IsQuasiIso.of_saturatedComp_left
    (hf.saturationExtension (f.hasCoherentPullbacks_of_saturated A.hasAllLocalDomains)) hcomp
  exact (AffinoidAtlasPresentation.CompatibleStrongHom.isQuasiIso_saturationExtension_iff
    (compatibleFunctor.map g)).mp hg

/-- Two consecutive full quasi-isomorphism composites force all three
factors to be full quasi-isomorphisms. -/
theorem isQuasiIso_twoOutOfSix (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (hfg : (f ≫ g).IsQuasiIso) (hgh : (g ≫ h).IsQuasiIso) :
    f.IsQuasiIso ∧ g.IsQuasiIso ∧ h.IsQuasiIso := by
  have hginj : Function.Injective g.baseMap := by
    intro x y hxy
    apply hgh.1.injective
    exact congrArg h.baseMap hxy
  let eg : B.presentation.space ≃ₜ C.presentation.space :=
    { toFun := g.baseMap
      invFun := fun y => f.baseMap (hfg.1.homeomorph.symm y)
      left_inv := fun y => hginj (hfg.1.homeomorph.apply_symm_apply (g.baseMap y))
      right_inv := fun y => hfg.1.homeomorph.apply_symm_apply y
      continuous_toFun := g.baseMap.continuous
      continuous_invFun := f.baseMap.continuous.comp hfg.1.homeomorph.symm.continuous }
  have hfhome : IsHomeomorph f.baseMap := by
    have he : eg.symm ∘ (f ≫ g).baseMap = f.baseMap := by
      funext x
      exact eg.symm_apply_apply (f.baseMap x)
    exact he ▸ eg.symm.isHomeomorph.comp hfg.1
  have hf : f.IsQuasiIso := by
    refine ⟨hfhome, ?_⟩
    intro i j hfij
    obtain ⟨k, hgjk⟩ := g.target_exists j
    obtain ⟨l, hhkl⟩ := h.target_exists k
    have hfik := f.comp_admissible g i j k hfij hgjk
    have hgjl := g.comp_admissible h j k l hgjk hhkl
    have hrepfg : Represents K ((f.pullback i j hfij).comp (g.pullback j k hgjk))
        ((f ≫ g).chartImageLocus i k) :=
      (congrArg (fun m => Represents K m ((f ≫ g).chartImageLocus i k))
        (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback f g
          A.hasAllLocalDomains B.hasAllLocalDomains i j k hfij hgjk hfik)).mp
            (hfg.2 i k hfik)
    have hrepgh : Represents K ((g.pullback j k hgjk).comp (h.pullback k l hhkl))
        ((g ≫ h).chartImageLocus j l) :=
      (congrArg (fun m => Represents K m ((g ≫ h).chartImageLocus j l))
        (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback g h
          B.hasAllLocalDomains C.hasAllLocalDomains j k l hgjk hhkl hgjl)).mp
            (hgh.2 j l hgjl)
    have hr := hrepfg.of_comp_of_comp hrepgh
    have hl : (BanachSpectrum.comap (g.pullback j k hgjk).toBoundedRingHom) ⁻¹'
        (f ≫ g).chartImageLocus i k = f.chartImageLocus i j := by
      ext x
      change C.presentation.atlas.chart k
        (BanachSpectrum.comap (g.pullback j k hgjk).toBoundedRingHom x) ∈
          (g.baseMap.comp f.baseMap) '' Set.range (A.presentation.atlas.chart i) ↔
        B.presentation.atlas.chart j x ∈ f.baseMap '' Set.range (A.presentation.atlas.chart i)
      rw [g.chart_comm]
      constructor
      · rintro ⟨z, hz, he⟩
        exact ⟨z, hz, hginj he⟩
      · rintro ⟨z, hz, he⟩
        exact ⟨z, hz, congrArg g.baseMap he⟩
    exact (congrArg (Represents K (f.pullback i j hfij)) hl).mp hr
  have hg := isQuasiIso_of_comp_left hf hfg
  exact ⟨hf, hg, isQuasiIso_of_comp_left hg hgh⟩

end SaturatedAtlasPresentation

end Langlands.Analytic
