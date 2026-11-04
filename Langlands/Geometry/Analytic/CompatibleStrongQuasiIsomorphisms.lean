import Langlands.Geometry.Analytic.CompatibleStrongOriginalRestriction
import Langlands.Geometry.Analytic.SaturatedStrongQuasiIsomorphisms

/-! # Actual quasi-isomorphisms and the full saturation comparison -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra

/-- Equality of the full presented endpoints and heterogeneous equality of
bounded maps transport the full representation of their actual spectrum range. -/
theorem represents_range_iff_of_heq
    {R R' S S' : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S')
    {p : BoundedAlgHom K S R} {p' : BoundedAlgHom K S' R'} (hp : HEq p p') :
    Represents K p (Set.range (BanachSpectrum.comap p.toBoundedRingHom)) ↔
      Represents K p' (Set.range (BanachSpectrum.comap p'.toBoundedRingHom)) := by
  cases hR
  cases hS
  cases eq_of_heq hp
  rfl

end PresentedAffinoidAlgebra

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Every constructed source-domain map to an original target chart is a
full representation when the original map is a full quasi-isomorphism. -/
theorem IsQuasiIso.represents_localChartPullback {f : StrongHom A B}
    (hf : f.IsQuasiIso) (U : LocalDomain A.atlas) (j : B.atlas.Index)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j)) :
    Represents K (f.localChartPullback U j h)
      (B.atlas.chart j ⁻¹' (f.baseMap '' U.locus)) := by
  let k := f.chosenTargetIndex U.index
  have hparent := (hf.2 U.index k (f.chosenTarget_admissible U.index)).comp_of_injective
    U.domain.represents (hf.isEmbedding_pullback U.index k
      (f.chosenTarget_admissible U.index)).injective
  have himage : B.atlas.mapChartImage k U.algebra
      (f.mapAffinoidChart U.index k (f.chosenTarget_admissible U.index)
        U.algebra U.domain.baseMap) = f.baseMap '' U.locus := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      dsimp only
      rw [f.mapAffinoidChart_chart]
      exact ⟨U.ambientMap x,
        ⟨U.domain.spectrumMap x, U.domain.represents.hasImageIn x, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨t, ht⟩ := U.domain.represents.2.1.symm ▸ hz
      refine ⟨t, ?_⟩
      dsimp only
      rw [f.mapAffinoidChart_chart]
      exact congrArg f.baseMap (congrArg (A.atlas.chart U.index) ht)
  have hc := B.atlas.represents_changeMapChart k j U.algebra
    (f.mapAffinoidChart U.index k (f.chosenTarget_admissible U.index)
      U.algebra U.domain.baseMap) hparent (f.localDomain_parentPullback_image U j h)
  rw [himage] at hc
  exact hc

/-- Factoring through a full target domain retains the full affinoid-test
representation of the actual source-domain image. -/
theorem IsQuasiIso.represents_localDomainPullback {f : StrongHom A B}
    (hf : f.IsQuasiIso) (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) :
    Represents K (f.localDomainPullback U V h)
      (V.ambientMap ⁻¹' (f.baseMap '' U.locus)) := by
  have hparent := hf.represents_localChartPullback U V.index
    (f.localDomain_parent_admissible U V h)
  rw [← f.localDomainPullback_comp_baseMap U V h] at hparent
  exact V.domain.represents.of_comp_of_injective hparent
    V.domain.spectrumMap_injective

/-- The actual extension preserves the original full quasi-isomorphism
condition at every new pair of local domains. -/
theorem IsQuasiIso.saturationExtension {f : StrongHom A B}
    (hf : f.IsQuasiIso) (hc : f.HasCoherentPullbacks) :
    (f.saturationExtension hc).IsQuasiIso := by
  refine ⟨hf.1, ?_⟩
  intro S T h
  have hlocal : f.baseMap '' (A.atlas.saturatedRepresentative S).locus ⊆
      (B.atlas.saturatedRepresentative T).locus := by
    rw [← (A.atlas.saturatedRepresentative S).range_ambientMap,
      ← (B.atlas.saturatedRepresentative T).range_ambientMap]
    exact h
  change Represents K (f.localDomainPullback
    (A.atlas.saturatedRepresentative S) (B.atlas.saturatedRepresentative T) hlocal)
    ((B.atlas.saturatedRepresentative T).ambientMap ⁻¹'
      (f.baseMap '' Set.range (A.atlas.saturatedRepresentative S).ambientMap))
  rw [(A.atlas.saturatedRepresentative S).range_ambientMap]
  exact hf.represents_localDomainPullback (A.atlas.saturatedRepresentative S)
    (B.atlas.saturatedRepresentative T) hlocal

/-- Restriction of any full quasi-isomorphism between constructed enlargements
retains its full representation at every original admissible chart pair. -/
theorem IsQuasiIso.originalRestriction
    {F : StrongHom A.saturatedPresentation B.saturatedPresentation}
    (hF : F.IsQuasiIso) : F.originalRestriction.toStrongHom.IsQuasiIso := by
  refine ⟨hF.1, ?_⟩
  intro i j h
  rw [← F.originalRestriction.toStrongHom.range_pullback i j h]
  apply (represents_range_iff_of_heq
    (A.atlas.saturatedAtlas_original_algebra i)
    (B.atlas.saturatedAtlas_original_algebra j) (F.originalPullback_heq i j h).symm).mp
  let I : A.saturatedPresentation.atlas.Index := A.atlas.originalSaturatedIndex i
  let J : B.saturatedPresentation.atlas.Index := B.atlas.originalSaturatedIndex j
  have hIJ := F.original_admissible i j h
  exact (congrArg (Represents K (F.pullback I J hIJ))
    (F.range_pullback I J hIJ)).mpr (hF.2 I J hIJ)

end AffinoidAtlasPresentation.StrongHom

namespace AffinoidAtlasPresentation.CompatibleStrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Saturation identifies precisely the original all-test quasi-isomorphism
condition; neither direction replaces bounded maps by spectrum data. -/
theorem isQuasiIso_saturationExtension_iff (f : CompatibleStrongHom A B) :
    f.saturationExtension.IsQuasiIso ↔ f.toStrongHom.IsQuasiIso := by
  constructor
  · intro h
    have hr := h.originalRestriction
    rw [f.originalRestriction_saturationExtension] at hr
    exact hr
  · intro h
    exact h.saturationExtension f.coherent

/-- Full quasi-isomorphisms compose in the original compatible category. -/
theorem isQuasiIso_comp {f : CompatibleStrongHom A B} {g : CompatibleStrongHom B C}
    (hf : f.toStrongHom.IsQuasiIso) (hg : g.toStrongHom.IsQuasiIso) :
    (f.comp g).toStrongHom.IsQuasiIso := by
  apply ((f.comp g).isQuasiIso_saturationExtension_iff).mp
  rw [saturationExtension_comp]
  exact ((f.isQuasiIso_saturationExtension_iff).mpr hf).saturatedComp
    ((g.isQuasiIso_saturationExtension_iff).mpr hg)
    A.atlas.saturatedAtlas_hasAllLocalDomains B.atlas.saturatedAtlas_hasAllLocalDomains

end AffinoidAtlasPresentation.CompatibleStrongHom

namespace CompatibleAtlasPresentation

/-- Original full quasi-isomorphisms with the actual compatible bounded families. -/
def quasiIsomorphisms : MorphismProperty (CompatibleAtlasPresentation.{u, v, w} K) :=
  fun _ _ f => f.toStrongHom.IsQuasiIso

@[simp]
theorem quasiIsomorphisms_iff {A B : CompatibleAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) : quasiIsomorphisms f ↔ f.toStrongHom.IsQuasiIso := Iff.rfl

instance : (quasiIsomorphisms (K := K)).IsMultiplicative where
  id_mem A := AffinoidAtlasPresentation.StrongHom.isQuasiIso_id A.presentation
  comp_mem _ _ hf hg := AffinoidAtlasPresentation.CompatibleStrongHom.isQuasiIso_comp hf hg

/-- The actual saturation functor preserves and reflects the specified class. -/
@[simp]
theorem quasiIsomorphisms_saturationFunctor_map_iff
    {A B : CompatibleAtlasPresentation.{u, v, w} K} (f : A ⟶ B) :
    SaturatedAtlasPresentation.quasiIsomorphisms (saturationFunctor.map f) ↔
      quasiIsomorphisms f := f.isQuasiIso_saturationExtension_iff

end CompatibleAtlasPresentation
end Langlands.Analytic
