import Langlands.Geometry.Analytic.FiniteEtaleChartGluing
import Langlands.Geometry.Analytic.FiniteEtaleAffinoidHomDescentStatement
import Langlands.Geometry.Analytic.AffinoidChartLiftTopology
import Langlands.Geometry.Analytic.DistinguishedOpenRestriction
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Geometry.Analytic.LocalizedDomainBaseChange

/-! # Reduction of arbitrary-target descent to images of rational domains -/

noncomputable section

universe u v

namespace Langlands.Analytic

open _root_.CategoryTheory Set PresentedAffinoidAlgebra
open scoped Topology

namespace AtlasTopology

private theorem IsQuasinet.image_of_isOpenMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {τ : Set (Set X)} (hτ : IsQuasinet τ) (f : X → Y)
    (hf : IsOpenMap f) (hsurj : Function.Surjective f) : IsQuasinet (image f '' τ) := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨σ, hσ, hsub, hx, hn⟩ := hτ x
  refine ⟨image f '' σ, hσ.image _, image_mono hsub, ?_, ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨x, hx U hU, rfl⟩
  · rw [← image_sUnion]
    exact hf.image_mem_nhds hn

end AtlasTopology

namespace SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum A)]
  [Small.{v} (BanachSpectrum B)]

private theorem isOriginalChartDomain_iUnion_of_isClosed
    {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, v} K X)
    {n : ℕ} (D : Fin n → Set X) (hD : ∀ i, a.IsOriginalChartDomain (D i))
    (hc : ∀ i, IsClosed (D i)) : a.IsOriginalChartDomain (⋃ i, D i) := by
  classical
  have aux (J : Finset (Fin n)) : a.IsOriginalChartDomain (⋃ i ∈ J, D i) := by
    induction J using Finset.induction_on with
    | empty =>
      simpa only [Finset.notMem_empty, iUnion_false, iUnion_empty] using
        a.isOriginalChartDomain_empty
    | insert i J _ ih =>
      change a.IsOriginalChartDomain (⋃ j ∈ (↑(insert i J) : Set (Fin n)), D j)
      rw [Finset.coe_insert, biUnion_insert]
      exact (hD i).union_of_isClosed ih (hc i)
        (J.finite_toSet.isClosed_biUnion fun j _ => hc j)
  simpa only [Finset.mem_univ, iUnion_true] using aux Finset.univ

/-- An image-domain result for ambient rational charts implies the corresponding
result for all charts of the saturated affinoid spectrum. -/
theorem isOriginalChartDomain_image_chart_of_rational
    (f : BoundedAlgHom K A B)
    (himage : ∀ D : RationalChart K B,
      (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.IsOriginalChartDomain
        (SmallAffinoidSpectrum.spectrumHomeomorph.{u, v} A ''
          (BanachSpectrum.comap f.toBoundedRingHom '' D.locus)))
    (c : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.atlas.Index) :
    (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.IsOriginalChartDomain
      ((SmallAffinoidSpectrum.map f).baseMap ''
        range ((SmallAffinoidSpectrum.saturated.{u, v} B).presentation.atlas.chart c)) := by
  let b := (SmallAffinoidSpectrum.presentation.{u, v} B).atlas
  let U := b.saturatedRepresentative c
  let D : Domain K B := U.domain
  let eB : BanachSpectrum B → (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.space :=
    SmallAffinoidSpectrum.spectrumHomeomorph B
  let eA : BanachSpectrum A → (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.space :=
    SmallAffinoidSpectrum.spectrumHomeomorph A
  let p : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.space →
      (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.space :=
    (SmallAffinoidSpectrum.map f).baseMap
  have hc : range ((SmallAffinoidSpectrum.saturated.{u, v} B).presentation.atlas.chart c) =
      eB '' D.locus := U.range_ambientMap
  have hπ (S : Set (BanachSpectrum B)) :
      p '' (eB '' S) = eA '' (BanachSpectrum.comap f.toBoundedRingHom '' S) := by
    rw [image_image]
    rw [image_image]
    exact congrArg (fun m => m '' S)
      (funext (SmallAffinoidSpectrum.map_spectrumHomeomorph.{u, v} f))
  let C := D.finiteRationalCoverData
  have hcover : (⋃ i, (C.chart i).locus) = D.locus := by
    ext x
    exact ⟨fun hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact (C.map i).subset hi, fun hx => mem_iUnion.mpr (C.covers x hx)⟩
  change (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.IsOriginalChartDomain
    (p '' range ((SmallAffinoidSpectrum.saturated.{u, v} B).presentation.atlas.chart c))
  rw [hc, hπ, ← hcover, image_iUnion, image_iUnion]
  have : T2Space (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.space :=
    (SmallAffinoidSpectrum.spectrumHomeomorph.{u, v} A).symm.isEmbedding.t2Space
  have heA : Continuous eA :=
    (SmallAffinoidSpectrum.spectrumHomeomorph.{u, v} A).continuous
  apply isOriginalChartDomain_iUnion_of_isClosed _ _ (fun i => himage (C.chart i))
  intro i
  exact ((((C.chart i).toDomain.isCompact_locus.image
    (BanachSpectrum.comapContinuous f.toBoundedRingHom).continuous).image heA).isClosed)

/-- If the image of every source chart is an analytic domain, the charts on the base
whose inverse images map into target charts locally refine the base. -/
theorem locallyRefines_goodBaseChart_of_chart_images (f : BoundedAlgHom K A B)
    (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom))
    (himage : ∀ c : (SmallAffinoidSpectrum.saturated.{u, v} B).presentation.atlas.Index,
      (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.IsOriginalChartDomain
        ((SmallAffinoidSpectrum.map f).baseMap ''
          range ((SmallAffinoidSpectrum.saturated.{u, v} B).presentation.atlas.chart c)))
    (T : SaturatedAtlasPresentation.{u, v, v} K)
    (g : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B) ⟶
      localizationFunctor.obj T)
    (hg : ∀ (Z : LocalizedCategory.{u, v, v} (K := K))
      (a b : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
      a ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) =
          b ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) → a ≫ g = b ≫ g) :
    AtlasTopology.LocallyRefines
      (range fun c : {c // GoodBaseChart f T g c} =>
        range ((SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.chart c.val))
      {univ} := by
  let S := SmallAffinoidSpectrum.saturated.{u, v} B
  let R := SmallAffinoidSpectrum.saturated.{u, v} A
  let p : S.presentation.space → R.presentation.space := (SmallAffinoidSpectrum.map f).baseMap
  let γ : S.presentation.space → T.presentation.space := localizedSpaceFunctor.map g
  let τ := range fun c : {c : S.presentation.atlas.Index // ∃ e : T.presentation.atlas.Index,
      range (S.presentation.atlas.chart c) ⊆ γ ⁻¹' range (T.presentation.atlas.chart e)} =>
    range (S.presentation.atlas.chart c.val)
  let υ := range fun c : {c // GoodBaseChart f T g c} =>
    range (R.presentation.atlas.chart c.val)
  have hτ : AtlasTopology.IsQuasinet τ := by
    apply (T.presentation.atlas.isNet_chartFamily.1.preimage_image
      (f := γ) (localizedSpaceFunctor.map g).hom.continuous).refine
    rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩ y hy
    have hD : S.presentation.atlas.IsOriginalChartDomain
        (γ ⁻¹' range (T.presentation.atlas.chart e)) :=
      isOriginalChartDomain_preimage g (T.chartDomain e)
    obtain ⟨σ, hσ, hs, hm, hn⟩ := (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hD
      _ (mem_singleton _) y hy
    refine ⟨σ, hσ, ?_, hm, hn⟩
    intro V hV
    obtain ⟨c, rfl⟩ := hs hV
    exact ⟨⟨c, e, (hm _ hV).1⟩, rfl⟩
  have hπet : etale (localizationFunctor.map (SmallAffinoidSpectrum.map.{u, v} f)) :=
    SmallAffinoidSpectrum.map_etale_of_finite_pointwiseEtale f
      AffinoidPushout.finiteBanachPushout AffinoidPushout.finiteTensorComparison hf
      (fun s => he.isEtaleAtPoint s)
  have hp : IsOpenMap p := by
    have h := etaleOpenMap K _ hπet
    rw [localizedSpaceFunctor_map] at h
    exact h
  have hps : Function.Surjective p := by
    have h := surjective_localizedSpaceFunctor_map_map f hsurj
    rw [localizedSpaceFunctor_map] at h
    exact h
  have hυ : AtlasTopology.LocallyRefines υ (image p '' τ) := by
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩ x hx
    obtain ⟨σ, hσ, hs, hm, hn⟩ :=
      (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp (himage c.val)
        _ (mem_singleton _) x hx
    refine ⟨σ, hσ, ?_, hm, hn⟩
    intro V hV
    obtain ⟨d, rfl⟩ := hs hV
    obtain ⟨e, hce⟩ := c.property
    refine ⟨⟨d, e, ?_⟩, rfl⟩
    intro y hy
    obtain ⟨z, hz, hzy⟩ := (hm _ hV).1 hy
    rw [← map_eq_of_baseMap_eq f hf g hg z y hzy]
    exact hce hz
  rintro _ rfl x -
  obtain ⟨σ, hσ, hs, hm, hn⟩ := (hτ.image_of_isOpenMap p hp hps).refine hυ x
  exact ⟨σ, hσ, hs, fun V hV => ⟨subset_univ V, hm V hV⟩, by rwa [nhdsWithin_univ]⟩

/-- Recognition of images of single rational charts under finite étale affinoid
maps suffices for descent into arbitrary localized targets. -/
theorem finiteEtaleAffinoidHomDescent_of_rationalImages
    (himage : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (A B : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum A)]
      [Small.{v} (BanachSpectrum B)] (f : BoundedAlgHom K A B),
      f.IsFiniteBanach → f.AlgebraicallyFiniteEtale → ∀ D : RationalChart K B,
        (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.IsOriginalChartDomain
          (SmallAffinoidSpectrum.spectrumHomeomorph.{u, v} A ''
            (BanachSpectrum.comap f.toBoundedRingHom '' D.locus))) :
    FiniteEtaleAffinoidHomDescentStatement.{u, v} := by
  intro K _ _ _ A B _ _ f hf he hsurj T g hg
  obtain ⟨T₀, rfl⟩ := localizedObjectEquiv.surjective T
  exact exists_hom_of_finiteEtale_of_locallyRefines f hf he hsurj T₀ g hg
    (locallyRefines_goodBaseChart_of_chart_images f hf he hsurj
      (isOriginalChartDomain_image_chart_of_rational f (himage K A B f hf he)) T₀ g hg)

end SaturatedAtlasPresentation

end Langlands.Analytic
