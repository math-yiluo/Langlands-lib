import Langlands.Geometry.Analytic.SaturatedStrongCategory
import Langlands.Geometry.Analytic.AtlasMapChartChangeRepresentation
import Langlands.Geometry.Analytic.StrongQuasiIsoComposition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCancellation

/-! # Full quasi-isomorphisms in the saturated strong-map category -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- The ambient image of an original bounded chain is exactly the image of
the original source chart under the literal composite continuous map. -/
theorem mapChartImage_chainPullback (f : StrongHom A B) (g : StrongHom B C)
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k)) :
    C.atlas.mapChartImage k (A.atlas.algebra i) (f.chainPullback g i j k hf hg) =
      (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) := by
  change Set.range (fun x => C.atlas.chart k
    (BanachSpectrum.comap (f.chainPullback g i j k hf hg).toBoundedRingHom x)) = _
  simp_rw [f.chainPullback_chart g i j k hf hg]
  exact Set.range_comp (g.baseMap.comp f.baseMap) (A.atlas.chart i)

/-- Full quasi-isomorphisms compose by actual bounded domain composition and
arbitrary target-chart change. The final atlas need not be saturated. -/
theorem IsQuasiIso.saturatedComp {f : StrongHom A B} {g : StrongHom B C}
    (hf : f.IsQuasiIso) (hg : g.IsQuasiIso)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains) :
    (f.saturatedComp g ha hb).IsQuasiIso := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro i k h
  obtain ⟨j, hfij⟩ := f.target_exists i
  obtain ⟨p, hgjp⟩ := g.target_exists j
  have hchain := (hg.2 j p hgjp).comp_of_injective (hf.2 i j hfij)
    (hg.isEmbedding_pullback j p hgjp).injective
  have hchange := C.atlas.represents_changeMapChart p k (A.atlas.algebra i)
    (f.chainPullback g i j p hfij hgjp) hchain
    (f.chainPullback_image_chart g i j p k hfij hgjp h)
  rw [f.mapChartImage_chainPullback g i j p hfij hgjp] at hchange
  change PresentedAffinoidAlgebra.Represents K (f.saturatedCompPullback g i k h)
    (C.atlas.chart k ⁻¹' ((g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i)))
  rw [f.saturatedCompPullback_eq_chainChange g ha hb i j p k hfij hgjp h]
  exact hchange

private theorem pullback_eq_of_strongHom_eq {f g : StrongHom A B} (heq : f = g)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    f.pullback i j hf = g.pullback i j hg := by
  subst g
  rfl

/-- Postcomposition along a full quasi-isomorphism cancels complete strong
maps. Both source atlases are saturated; the final atlas is arbitrary. -/
theorem IsQuasiIso.cancel_saturatedComp {s : StrongHom B C}
    (hs : s.IsQuasiIso) (ha : A.atlas.HasAllLocalDomains)
    (hb : B.atlas.HasAllLocalDomains) {f g : StrongHom A B}
    (heq : f.saturatedComp s ha hb = g.saturatedComp s ha hb) : f = g := by
  have hbase : f.baseMap = g.baseMap := by
    ext x
    apply hs.1.homeomorph.injective
    exact congrArg (fun F : StrongHom A C => F.baseMap x) heq
  refine ext_of_saturated ha hbase ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  have hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) := by
    rw [← hbase]
    exact hf
  obtain ⟨k, hsmap⟩ := s.target_exists j
  have hfs := f.comp_admissible s i j k hf hsmap
  have hgs := g.comp_admissible s i j k hg hsmap
  refine ⟨j, hf, ?_⟩
  apply (hs.2 j k hsmap).hom_ext (A.atlas.algebra i)
  have hlocal := pullback_eq_of_strongHom_eq heq i k hfs hgs
  rw [saturatedComp_pullback f s ha hb i j k hf hsmap hfs,
    saturatedComp_pullback g s ha hb i j k hg hsmap hgs] at hlocal
  exact hlocal

theorem IsQuasiIso.saturatedComp_eq_iff {s : StrongHom B C}
    (hs : s.IsQuasiIso) (ha : A.atlas.HasAllLocalDomains)
    (hb : B.atlas.HasAllLocalDomains) (f g : StrongHom A B) :
    f.saturatedComp s ha hb = g.saturatedComp s ha hb ↔ f = g :=
  ⟨hs.cancel_saturatedComp ha hb, fun h =>
    congrArg (fun F => F.saturatedComp s ha hb) h⟩

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation

/-- Actual full strong quasi-isomorphisms in the saturated category, retaining
the full-domain condition at every admissible pair of original charts. -/
def quasiIsomorphisms : MorphismProperty (SaturatedAtlasPresentation.{u, v, w} K) :=
  fun _ _ f => f.IsQuasiIso

@[simp]
theorem quasiIsomorphisms_iff {A B : SaturatedAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) : quasiIsomorphisms f ↔ f.IsQuasiIso := Iff.rfl

instance : (quasiIsomorphisms (K := K)).IsMultiplicative where
  id_mem A := AffinoidAtlasPresentation.StrongHom.isQuasiIso_id A.presentation
  comp_mem {A B _C} _ _ hf hg := hf.saturatedComp hg A.hasAllLocalDomains B.hasAllLocalDomains

variable {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- A quasi-isomorphism is monic by the complete bounded domain uniqueness
property, together with saturated-source extensionality. -/
theorem mono_of_isQuasiIso (s : B ⟶ C) (hs : s.IsQuasiIso) : Mono s where
  right_cancellation {Z} _ _ h :=
    hs.cancel_saturatedComp Z.hasAllLocalDomains B.hasAllLocalDomains h

/-- The actual composition operation embeds hom sets along any full
quasi-isomorphism in the saturated category. -/
def postcompQuasiIsoEmbedding (s : B ⟶ C) (hs : s.IsQuasiIso) :
    (A ⟶ B) ↪ (A ⟶ C) where
  toFun f := f ≫ s
  inj' _ _ h := hs.cancel_saturatedComp A.hasAllLocalDomains B.hasAllLocalDomains h

@[simp]
theorem postcompQuasiIsoEmbedding_apply (s : B ⟶ C) (hs : s.IsQuasiIso)
    (f : A ⟶ B) :
    postcompQuasiIsoEmbedding s hs f = f ≫ s := rfl

end SaturatedAtlasPresentation

end Langlands.Analytic
