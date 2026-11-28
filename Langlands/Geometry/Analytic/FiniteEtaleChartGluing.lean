import Langlands.Geometry.Analytic.FiniteProjectiveBoundedDescent
import Langlands.Geometry.Analytic.LocalizedChartCoverGluing
import Langlands.Geometry.Analytic.EtaleCoverHomExt
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Langlands.Geometry.Analytic.LocalizedEtalePullbackPoints
import Langlands.Geometry.Analytic.SmallAffinoidEtaleRealization
import Langlands.Geometry.Analytic.SmallAffinoidPullbacks
import Langlands.Geometry.Analytic.SmallAffinoidPointwiseSquare
import Langlands.Geometry.Analytic.SmallAffinoidEtaleBaseChange
import Langlands.Geometry.Analytic.AffinoidPointwiseBaseChange
import Langlands.Geometry.Analytic.InvariantAnalyticDomains
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof
import Langlands.Geometry.Analytic.KeyLemma.QuasiEtaleStrongNearLifts

/-! # Descent along finite étale affinoid covers, chart by chart on the base -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace PresentedAffinoidAlgebra.AffinoidPushout

open scoped TensorProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

omit [CompleteSpace K] in
/-- Flatness of `f` passes to the right map of the affinoid pushout when the ordinary tensor
comparison is bijective. -/
theorem rightMap_flat_of_tensorComparison (h : Function.Bijective (tensorComparison f g))
    (hflat : f.toAlgHom.toRingHom.Flat) : (rightMap f g).toAlgHom.toRingHom.Flat := by
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra C (algebra f g) := (rightMap f g).toAlgHom.toRingHom.toAlgebra
  let e : C ⊗[A] B ≃ₐ[C] algebra f g :=
    { tensorComparisonEquiv f g h with
      commutes' := tensorComparison_tensorLeft f g }
  have : Module.Flat A B := hflat
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

/-- Surjectivity on Banach spectra passes from `f` to the right map of the affinoid
pushout. -/
theorem comap_rightMap_surjective
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom)) :
    Function.Surjective (BanachSpectrum.comap (rightMap f g).toBoundedRingHom) := by
  intro y
  obtain ⟨x, hx⟩ := hsurj (BanachSpectrum.comap g.toBoundedRingHom y)
  obtain ⟨z, -, hz⟩ := exists_point f g x y hx
  exact ⟨z, hz⟩

end PresentedAffinoidAlgebra.AffinoidPushout

namespace SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The localized small chart inclusion is the localized isomorphism onto the chart domain
followed by the canonical morphism of that domain. -/
theorem localizedChartIso_hom_comp (S : SaturatedAtlasPresentation.{u, v, v} K)
    (i : S.presentation.atlas.Index) :
    (localizationFunctor.mapIso (S.smallChartDomainIso i)).hom ≫
        localizationFunctor.map
          (S.originalDomainInclusion (IndexedAffinoidAtlas.OriginalChartDomain.ofChart i)) =
      localizationFunctor.map (S.smallChartSpectrumInclusion i) :=
  (localizationFunctor.map_comp _ _).symm.trans
    (congrArg localizationFunctor.map (smallChartDomainIso_hom_comp_inclusion S i))

/-- A localized morphism whose points land in a chart factors through the small spectrum of
that chart. -/
theorem exists_smallChartLift (S : SaturatedAtlasPresentation.{u, v, v} K)
    (i : S.presentation.atlas.Index) {Z : LocalizedCategory.{u, v, v} (K := K)}
    (φ : Z ⟶ localizationFunctor.obj S)
    (hφ : ∀ z, localizedSpaceFunctor.map φ z ∈ range (S.presentation.atlas.chart i)) :
    ∃ w : Z ⟶ localizationFunctor.obj (S.smallChartSpectrum i),
      w ≫ localizationFunctor.map (S.smallChartSpectrumInclusion i) = φ := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Z ⟶ localizationFunctor.obj
      (S.originalDomain (IndexedAffinoidAtlas.OriginalChartDomain.ofChart i)),
      ℓ ≫ localizationFunctor.map
        (S.originalDomainInclusion (IndexedAffinoidAtlas.OriginalChartDomain.ofChart i)) = φ :=
    exists_localizedDomainLift (S.chartDomain i) φ hφ
  refine ⟨ℓ ≫ (localizationFunctor.mapIso (S.smallChartDomainIso i)).inv, ?_⟩
  rw [← localizedChartIso_hom_comp, Category.assoc, Iso.inv_hom_id_assoc, hℓ]

/-- The localized small chart inclusion is a monomorphism. -/
theorem smallChartInclusion_cancel (S : SaturatedAtlasPresentation.{u, v, v} K)
    (i : S.presentation.atlas.Index) {Z : LocalizedCategory.{u, v, v} (K := K)}
    (a b : Z ⟶ localizationFunctor.obj (S.smallChartSpectrum i))
    (h : a ≫ localizationFunctor.map (S.smallChartSpectrumInclusion i) =
      b ≫ localizationFunctor.map (S.smallChartSpectrumInclusion i)) : a = b := by
  have : Mono (localizationFunctor.map
      (S.originalDomainInclusion (IndexedAffinoidAtlas.OriginalChartDomain.ofChart i))) :=
    S.localizedDomainInclusion_mono (S.chartDomain i)
  rw [← localizedChartIso_hom_comp, ← Category.assoc, ← Category.assoc] at h
  exact (cancel_mono _).1 ((cancel_mono _).1 h)

/-- Points of a composite of localized morphisms. -/
theorem localizedSpaceFunctor_map_comp_apply {X Y Z : LocalizedCategory.{u, v, v} (K := K)}
    (a : X ⟶ Y) (b : Y ⟶ Z) (x : localizedSpaceFunctor.obj X) :
    localizedSpaceFunctor.map (a ≫ b) x =
      localizedSpaceFunctor.map b (localizedSpaceFunctor.map a x) := by
  rw [Functor.map_comp]
  rfl

/-- A spectrum-surjective bounded map gives a localized map surjective on points. -/
theorem surjective_localizedSpaceFunctor_map_map {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)] (f : BoundedAlgHom K R S)
    (hf : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom)) :
    Function.Surjective
      (localizedSpaceFunctor.map (localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} f))) := by
  intro x
  rw [localizedSpaceFunctor_map]
  obtain ⟨z, rfl⟩ := (SmallAffinoidSpectrum.spectrumHomeomorph.{u, v} R).surjective x
  obtain ⟨y, hy⟩ := hf z
  refine ⟨SmallAffinoidSpectrum.spectrumHomeomorph.{u, v} S y, ?_⟩
  exact (SmallAffinoidSpectrum.map_spectrumHomeomorph.{u, v} f y).trans
    (congrArg (SmallAffinoidSpectrum.spectrumHomeomorph.{u, v} R) hy)

/-- A localized map `g : M(B) ⟶ T` equalizing all pairs identified by `M(f)`, for a finite
Banach map `f`, is constant on the fibres of `M(f)`. -/
theorem map_eq_of_baseMap_eq {A B : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum A)]
    [Small.{v} (BanachSpectrum B)] (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    {T : LocalizedCategory.{u, v, v} (K := K)}
    (g : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B) ⟶ T)
    (hg : ∀ (Z : LocalizedCategory.{u, v, v} (K := K))
      (a b : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
      a ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) =
          b ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) → a ≫ g = b ≫ g)
    (y y' : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.space)
    (h : (SmallAffinoidSpectrum.map f).baseMap y = (SmallAffinoidSpectrum.map f).baseMap y') :
    localizedSpaceFunctor.map g y = localizedSpaceFunctor.map g y' := by
  let : Small.{v} (BanachSpectrum (AffinoidPushout.algebra f f)) :=
    AffinoidPushout.small_spectrum_of_finiteBanachPushout f f
      AffinoidPushout.finiteBanachPushout hf
  obtain ⟨t, ht, ht'⟩ := SmallAffinoidSpectrum.pushout_exists_point.{u, v} f f y y' h
  have hw : localizationFunctor.map (SmallAffinoidSpectrum.pushoutFst.{u, v} f f) ≫ g =
      localizationFunctor.map (SmallAffinoidSpectrum.pushoutSnd.{u, v} f f) ≫ g := by
    apply hg
    rw [← Functor.map_comp, ← Functor.map_comp, SmallAffinoidSpectrum.pushout_condition]
  have h1 := ConcreteCategory.congr_hom (congrArg localizedSpaceFunctor.map hw) t
  have e1 : localizedSpaceFunctor.map
      (localizationFunctor.map (SmallAffinoidSpectrum.pushoutFst.{u, v} f f) ≫ g) t =
        localizedSpaceFunctor.map g y :=
    (localizedSpaceFunctor_map_comp_apply
        (localizationFunctor.map (SmallAffinoidSpectrum.pushoutFst.{u, v} f f)) g t).trans
      (congrArg (fun x : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.space =>
          localizedSpaceFunctor.map g x)
        ((localizedSpaceFunctor_map_apply (SmallAffinoidSpectrum.pushoutFst.{u, v} f f) t).trans
          ht))
  have e2 : localizedSpaceFunctor.map
      (localizationFunctor.map (SmallAffinoidSpectrum.pushoutSnd.{u, v} f f) ≫ g) t =
        localizedSpaceFunctor.map g y' :=
    (localizedSpaceFunctor_map_comp_apply
        (localizationFunctor.map (SmallAffinoidSpectrum.pushoutSnd.{u, v} f f)) g t).trans
      (congrArg (fun x : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.space =>
          localizedSpaceFunctor.map g x)
        ((localizedSpaceFunctor_map_apply (SmallAffinoidSpectrum.pushoutSnd.{u, v} f f) t).trans
          ht'))
  exact e1.symm.trans (h1.trans e2)

/-- Local descent over a base change. Let `f : A → B` be finite Banach, flat and surjective
on spectra, `ρ : A → C` a bounded map, and `g : M(B) ⟶ T` a localized map equalizing all
pairs identified by `M(f)`. Let `j : M(Q) ⟶ T` be a monomorphism from an affinoid space
through which every morphism with points in `U` factors. If `g` sends every point of `M(B)`
lying over the image of `M(C)` into `U`, then there is `l : M(C) ⟶ T` with
`w ≫ l = p ≫ g` whenever `w ≫ M(ρ) = p ≫ M(f)`. -/
theorem exists_baseChange_descent
    {A B C Q : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum A)]
    [Small.{v} (BanachSpectrum B)] [Small.{v} (BanachSpectrum C)]
    [Small.{v} (BanachSpectrum Q)]
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach) (hflat : f.toAlgHom.toRingHom.Flat)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom))
    (ρ : BoundedAlgHom K A C) {T : LocalizedCategory.{u, v, v} (K := K)}
    (g : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B) ⟶ T)
    (hg : ∀ (Z : LocalizedCategory.{u, v, v} (K := K))
      (a b : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
      a ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) =
          b ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) → a ≫ g = b ≫ g)
    (j : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} Q) ⟶ T)
    (hj : ∀ (Z : LocalizedCategory.{u, v, v} (K := K))
      (a b : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} Q)),
      a ≫ j = b ≫ j → a = b)
    (U : Set (localizedSpaceFunctor.obj T))
    (hU : ∀ (Z : LocalizedCategory.{u, v, v} (K := K)) (φ : Z ⟶ T),
      (∀ z, localizedSpaceFunctor.map φ z ∈ U) →
        ∃ w : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} Q),
          w ≫ j = φ)
    (hce : ∀ (x : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.space)
      (z : (SmallAffinoidSpectrum.saturated.{u, v} C).presentation.space),
      (SmallAffinoidSpectrum.map f).baseMap x = (SmallAffinoidSpectrum.map ρ).baseMap z →
        localizedSpaceFunctor.map g x ∈ U) :
    ∃ l : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} C) ⟶ T,
      ∀ (Z : LocalizedCategory.{u, v, v} (K := K))
        (w : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} C))
        (p : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
        w ≫ localizationFunctor.map (SmallAffinoidSpectrum.map ρ) =
            p ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) →
          w ≫ l = p ≫ g := by
  have hr : (AffinoidPushout.rightMap f ρ).IsFiniteBanach :=
    AffinoidPushout.finiteBanachPushout A B C f ρ hf
  have hrflat : (AffinoidPushout.rightMap f ρ).toAlgHom.toRingHom.Flat :=
    AffinoidPushout.rightMap_flat_of_tensorComparison f ρ
      (AffinoidPushout.finiteTensorComparison A B C f ρ hf) hflat
  have hrsurj : Function.Surjective
      (BanachSpectrum.comap (AffinoidPushout.rightMap f ρ).toBoundedRingHom) :=
    AffinoidPushout.comap_rightMap_surjective f ρ hsurj
  let : Small.{v} (BanachSpectrum (AffinoidPushout.algebra f ρ)) :=
    AffinoidPushout.small_spectrum_of_finiteBanachPushout f ρ
      AffinoidPushout.finiteBanachPushout hf
  have hpb : IsPullback
      (localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} (AffinoidPushout.leftMap f ρ)))
      (localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} (AffinoidPushout.rightMap f ρ)))
      (localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} f))
      (localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} ρ)) :=
    SmallAffinoidSpectrum.pushout_localized_isPullback.{u, v} f ρ
  have hcond : SmallAffinoidSpectrum.map.{u, v} (AffinoidPushout.leftMap f ρ) ≫
        SmallAffinoidSpectrum.map.{u, v} f =
      SmallAffinoidSpectrum.map.{u, v} (AffinoidPushout.rightMap f ρ) ≫
        SmallAffinoidSpectrum.map.{u, v} ρ :=
    SmallAffinoidSpectrum.pushout_condition.{u, v} f ρ
  have hφ : ∀ z, localizedSpaceFunctor.map (localizationFunctor.map
      (SmallAffinoidSpectrum.map.{u, v} (AffinoidPushout.leftMap f ρ)) ≫ g) z ∈ U := by
    intro z
    have h1 := (localizedSpaceFunctor_map_comp_apply (localizationFunctor.map
        (SmallAffinoidSpectrum.map.{u, v} (AffinoidPushout.leftMap f ρ))) g z).trans
      (congrArg (fun x : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.space =>
          localizedSpaceFunctor.map g x)
        (localizedSpaceFunctor_map_apply
          (SmallAffinoidSpectrum.map.{u, v} (AffinoidPushout.leftMap f ρ)) z))
    refine (congrArg (· ∈ U) h1).mpr ?_
    apply hce _ ((SmallAffinoidSpectrum.map.{u, v} (AffinoidPushout.rightMap f ρ)).baseMap z)
    have h := congrArg (fun F => F.baseMap z) hcond
    rw [baseMap_comp, baseMap_comp] at h
    exact h
  obtain ⟨m, hm⟩ := hU _ _ hφ
  have hmatch :
      localizationFunctor.map (SmallAffinoidSpectrum.finitePushoutFst
          (AffinoidPushout.rightMap f ρ) (AffinoidPushout.rightMap f ρ)
          AffinoidPushout.finiteBanachPushout hr) ≫ m =
        localizationFunctor.map (SmallAffinoidSpectrum.finitePushoutSnd
          (AffinoidPushout.rightMap f ρ) (AffinoidPushout.rightMap f ρ)
          AffinoidPushout.finiteBanachPushout hr) ≫ m := by
    apply hj
    rw [Category.assoc, Category.assoc, hm, ← Category.assoc, ← Category.assoc]
    apply hg
    rw [Category.assoc, Category.assoc, hpb.w, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Functor.map_comp, ← Functor.map_comp,
      SmallAffinoidSpectrum.finitePushout_condition (AffinoidPushout.rightMap f ρ)
        (AffinoidPushout.rightMap f ρ) AffinoidPushout.finiteBanachPushout hr]
  obtain ⟨h, hh, -⟩ := SmallAffinoidSpectrum.exists_unique_localizedHomDescent.{u, v}
    (AffinoidPushout.rightMap f ρ) hr hrflat hrsurj m hmatch
  refine ⟨h ≫ j, fun Z w p hwp => ?_⟩
  rw [← hpb.lift_snd p w hwp.symm, Category.assoc, ← Category.assoc _ h, hh, hm,
    ← Category.assoc, hpb.lift_fst]

/-- Local descent over one chart `c` of the base whose preimage `g` maps into the chart `e`
of the target. -/
theorem exists_chart_descent {A B : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum A)]
    [Small.{v} (BanachSpectrum B)]
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach) (hflat : f.toAlgHom.toRingHom.Flat)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom))
    (T : SaturatedAtlasPresentation.{u, v, v} K)
    (g : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B) ⟶
      localizationFunctor.obj T)
    (hg : ∀ (Z : LocalizedCategory.{u, v, v} (K := K))
      (a b : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
      a ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) =
          b ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) → a ≫ g = b ≫ g)
    (c : (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.Index)
    (e : T.presentation.atlas.Index)
    (hce : ∀ y : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.space,
      (SmallAffinoidSpectrum.map f).baseMap y ∈
          range ((SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.chart c) →
        localizedSpaceFunctor.map g y ∈ range (T.presentation.atlas.chart e)) :
    ∃ l : localizationFunctor.obj
        ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrum c) ⟶
        localizationFunctor.obj T,
      ∀ (Z : LocalizedCategory.{u, v, v} (K := K))
        (w : Z ⟶ localizationFunctor.obj
          ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrum c))
        (p : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
        w ≫ localizationFunctor.map
            ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrumInclusion c) =
            p ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) →
          w ≫ l = p ≫ g := by
  let : Small.{v} (BanachSpectrum
      ((SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.algebra c)) :=
    small_of_injective
      ((SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.isEmbedding_chart c).injective
  let : Small.{v} (BanachSpectrum (T.presentation.atlas.algebra e)) :=
    small_of_injective (T.presentation.atlas.isEmbedding_chart e).injective
  obtain ⟨ρ, hρ⟩ := (SmallAffinoidSpectrum.localizedMapEquiv.{u, v} A
    ((SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.algebra c)).surjective
      (localizationFunctor.map
        ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrumInclusion c))
  have hρ' : localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} ρ) =
      localizationFunctor.map
        ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrumInclusion c) := hρ
  have hρmem : ∀ z, (SmallAffinoidSpectrum.map.{u, v} ρ).baseMap z ∈
      range ((SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.chart c) := by
    intro z
    have hb : (SmallAffinoidSpectrum.map.{u, v} ρ).baseMap z =
        ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrumInclusion c).baseMap z :=
      (localizedSpaceFunctor_map_apply _ z).symm.trans
        ((ConcreteCategory.congr_hom (congrArg localizedSpaceFunctor.map hρ') z).trans
          (localizedSpaceFunctor_map_apply _ z))
    obtain ⟨t, ht⟩ := smallChartSpectrumInclusion_mem _ c z
    exact ⟨t, ht.trans hb.symm⟩
  obtain ⟨l, hl⟩ := exists_baseChange_descent (Q := T.presentation.atlas.algebra e)
    f hf hflat hsurj ρ g hg
    (localizationFunctor.map (T.smallChartSpectrumInclusion e))
    (fun Z a b h => smallChartInclusion_cancel T e a b h)
    (range (T.presentation.atlas.chart e))
    (fun Z φ hφ => exists_smallChartLift T e φ hφ)
    (fun x z hxz => by
      obtain ⟨t, ht⟩ := hρmem z
      exact hce x ⟨t, ht.trans hxz.symm⟩)
  exact ⟨l, fun Z w p hwp => hl Z w p ((congrArg (w ≫ ·) hρ').trans hwp)⟩
/-- Compatibility of local descents along an étale map surjective on points: if `l₁` and
`l₂` satisfy `w ≫ lᵢ = p ≫ g` whenever `w ≫ iᵢ = p ≫ π`, then `l₁` and `l₂` agree on
every pair of arrows identified by `i₁` and `i₂`. -/
theorem descent_compat_of_etale {X Y T V₁ V₂ W : LocalizedCategory.{u, v, v} (K := K)}
    (π : Y ⟶ X) (hπet : etale π) (hπsurj : Function.Surjective (localizedSpaceFunctor.map π))
    (g : Y ⟶ T) (i₁ : V₁ ⟶ X) (i₂ : V₂ ⟶ X) (l₁ : V₁ ⟶ T) (l₂ : V₂ ⟶ T)
    (hl₁ : ∀ (Z : LocalizedCategory.{u, v, v} (K := K)) (w : Z ⟶ V₁) (p : Z ⟶ Y),
      w ≫ i₁ = p ≫ π → w ≫ l₁ = p ≫ g)
    (hl₂ : ∀ (Z : LocalizedCategory.{u, v, v} (K := K)) (w : Z ⟶ V₂) (p : Z ⟶ Y),
      w ≫ i₂ = p ≫ π → w ≫ l₂ = p ≫ g)
    (a : W ⟶ V₁) (b : W ⟶ V₂) (hab : a ≫ i₁ = b ≫ i₂) : a ≫ l₁ = b ≫ l₂ := by
  obtain ⟨P, p, q, hpq, hq⟩ := localizedEtalePullbackBaseChange π (a ≫ i₁) hπet
  refine etaleCoverHomExt (fun _ : PUnit.{1} => q) (fun _ => hq)
    (fun z => ⟨PUnit.unit, ?_⟩) _ _ (fun _ => ?_)
  · obtain ⟨y, hy⟩ := hπsurj (localizedSpaceFunctor.map (a ≫ i₁) z)
    obtain ⟨t, -, ht⟩ := exists_point_of_isPullback_of_etale hpq hπet y z hy
    exact ⟨t, ht⟩
  · rw [← Category.assoc, ← Category.assoc,
      hl₁ P (q ≫ a) p (by rw [Category.assoc]; exact hpq.w.symm),
      hl₂ P (q ≫ b) p (by rw [Category.assoc, ← hab]; exact hpq.w.symm)]

/-- The good charts of the base for `g`: charts of `M(A)` over whose preimage `g` lands in a
single chart of `T`. -/
def GoodBaseChart {A B : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum A)]
    [Small.{v} (BanachSpectrum B)] (f : BoundedAlgHom K A B)
    (T : SaturatedAtlasPresentation.{u, v, v} K)
    (g : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B) ⟶
      localizationFunctor.obj T)
    (c : (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.Index) : Prop :=
  ∃ e : T.presentation.atlas.Index,
    ∀ y : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.space,
      (SmallAffinoidSpectrum.map f).baseMap y ∈
          range ((SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.chart c) →
        localizedSpaceFunctor.map g y ∈ range (T.presentation.atlas.chart e)

/-- Descent along a finite Banach, algebraically finite étale, spectrum-surjective map
`f : A → B`, for a localized map `g : M(B) ⟶ T` equalizing all pairs identified by `M(f)`,
provided the charts of `M(A)` over whose preimage `g` lands in a single chart of `T` locally
refine `M(A)`. -/
theorem exists_hom_of_finiteEtale_of_locallyRefines
    {A B : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum A)]
    [Small.{v} (BanachSpectrum B)]
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom))
    (T : SaturatedAtlasPresentation.{u, v, v} K)
    (g : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B) ⟶
      localizationFunctor.obj T)
    (hg : ∀ (Z : LocalizedCategory.{u, v, v} (K := K))
      (a b : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
      a ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) =
          b ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) → a ≫ g = b ≫ g)
    (hloc : AtlasTopology.LocallyRefines
      (range fun c : {c // GoodBaseChart f T g c} =>
        range ((SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.chart c.val))
      {univ}) :
    ∃ h : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} A) ⟶
        localizationFunctor.obj T,
      localizationFunctor.map (SmallAffinoidSpectrum.map f) ≫ h = g := by
  classical
  have hflat : f.toAlgHom.toRingHom.Flat :=
    ((BoundedAlgHom.algebraicallyFiniteEtale_iff f).1 he).2.1
  have hπet : etale (localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} f)) :=
    SmallAffinoidSpectrum.map_etale_of_finite_pointwiseEtale f
      AffinoidPushout.finiteBanachPushout AffinoidPushout.finiteTensorComparison hf
      (fun s => he.isEtaleAtPoint s)
  have hπsurj := surjective_localizedSpaceFunctor_map_map f hsurj
  have hlocal : ∀ k : {c // GoodBaseChart f T g c},
      ∃ l : localizationFunctor.obj
          ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrum k.val) ⟶
          localizationFunctor.obj T,
        ∀ (Z : LocalizedCategory.{u, v, v} (K := K))
          (w : Z ⟶ localizationFunctor.obj
            ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrum k.val))
          (p : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
          w ≫ localizationFunctor.map
              ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrumInclusion k.val) =
              p ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) →
            w ≫ l = p ≫ g := fun k =>
    exists_chart_descent f hf hflat hsurj T g hg k.val k.property.choose k.property.choose_spec
  choose l hl using hlocal
  have hcompat : ∀ (k j : {c // GoodBaseChart f T g c}) (Z : LocalizedCategory.{u, v, v} (K := K))
      (a : Z ⟶ localizationFunctor.obj
        ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrum k.val))
      (b : Z ⟶ localizationFunctor.obj
        ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrum j.val)),
      a ≫ localizationFunctor.map
          ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrumInclusion k.val) =
        b ≫ localizationFunctor.map
          ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrumInclusion j.val) →
      a ≫ l k = b ≫ l j := fun k j Z a b hab =>
    descent_compat_of_etale _ hπet hπsurj g _ _ (l k) (l j) (hl k) (hl j) a b hab
  obtain ⟨L, hL⟩ := exists_hom_of_chartCover
    (A := SmallAffinoidSpectrum.saturated.{u, v} A)
    (fun k : {c // GoodBaseChart f T g c} => k.val) hloc (Y := localizationFunctor.obj T) l
    hcompat
  have hL' : ∀ k : {c // GoodBaseChart f T g c},
      localizationFunctor.map
          ((SmallAffinoidSpectrum.saturated.{u, v} A).smallChartSpectrumInclusion k.val) ≫ L =
        l k := hL
  refine ⟨L, ?_⟩
  have hrefine := locallyRefines_charts_into (SmallAffinoidSpectrum.map.{u, v} f)
    (fun k : {c // GoodBaseChart f T g c} => k.val) hloc
  refine localizedHom_ext_of_chartCover
    (A := SmallAffinoidSpectrum.saturated.{u, v} B) _ hrefine _ _ ?_
  rintro ⟨⟨k, d⟩, hkd⟩
  change localizationFunctor.map
      ((SmallAffinoidSpectrum.saturated.{u, v} B).smallChartSpectrumInclusion d) ≫
        localizationFunctor.map (SmallAffinoidSpectrum.map f) ≫ L =
    localizationFunctor.map
      ((SmallAffinoidSpectrum.saturated.{u, v} B).smallChartSpectrumInclusion d) ≫ g
  obtain ⟨w, hw⟩ := exists_smallChartLift (SmallAffinoidSpectrum.saturated.{u, v} A) k.val
    (localizationFunctor.map
        ((SmallAffinoidSpectrum.saturated.{u, v} B).smallChartSpectrumInclusion d) ≫
      localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} f)) (by
      intro x
      have h1 := (localizedSpaceFunctor_map_comp_apply (localizationFunctor.map
          ((SmallAffinoidSpectrum.saturated.{u, v} B).smallChartSpectrumInclusion d))
          (localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} f)) x).trans
        ((localizedSpaceFunctor_map_apply (SmallAffinoidSpectrum.map.{u, v} f) _).trans
          (congrArg (SmallAffinoidSpectrum.map.{u, v} f).baseMap
            (localizedSpaceFunctor_map_apply
              ((SmallAffinoidSpectrum.saturated.{u, v} B).smallChartSpectrumInclusion d) x)))
      refine (congrArg (· ∈ range
        ((SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.chart k.val)) h1).mpr ?_
      exact hkd ⟨_, smallChartSpectrumInclusion_mem _ d x, rfl⟩)
  rw [← Category.assoc, ← hw, Category.assoc, hL' k, hl k _ w _ hw]

end SaturatedAtlasPresentation

end Langlands.Analytic
