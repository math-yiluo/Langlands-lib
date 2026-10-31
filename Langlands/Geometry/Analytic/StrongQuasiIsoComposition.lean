import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms
import Langlands.Geometry.Analytic.DirectedAtlasComposition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainComposition
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-! # Full quasi-isomorphisms under directed strong composition -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra

/-- If a bounded composite represents a full domain, its second structural
map represents the inverse-image locus in a full embedded outer domain. -/
theorem Represents.of_comp_of_injective {A B C : PresentedAffinoidAlgebra K}
    {i : BoundedAlgHom K A B} {j : BoundedAlgHom K B C}
    {U V : Set (BanachSpectrum A)} (hi : Represents K i U)
    (hij : Represents K (j.comp i) V)
    (hinj : Function.Injective (BanachSpectrum.comap i.toBoundedRingHom)) :
    Represents K j ((BanachSpectrum.comap i.toBoundedRingHom) ⁻¹' V) := by
  refine ⟨hij.1.preimage (BanachSpectrum.comapContinuous i.toBoundedRingHom).continuous,
    ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hij.hasImageIn y
    · intro hx
      obtain ⟨y, hy⟩ := hij.2.1.symm ▸ hx
      exact ⟨y, hinj hy⟩
  · intro R φ hφ
    have hφi : HasImageIn K (φ.comp i) V := by
      intro x
      exact hφ x
    obtain ⟨ψ, hψ, huniq⟩ := hij.2.2 R (φ.comp i) hφi
    refine ⟨ψ, ?_, ?_⟩
    · have hU : HasImageIn K (φ.comp i) U := by
        intro x
        exact hi.hasImageIn (BanachSpectrum.comap φ.toBoundedRingHom x)
      exact (hi.2.2 R (φ.comp i) hU).unique hψ rfl
    · intro χ hχ
      apply huniq χ
      change (χ.comp j).comp i = φ.comp i
      rw [hχ]

end PresentedAffinoidAlgebra

namespace IndexedAffinoidAtlas

/-- The spectrum restriction is embedded because its composite with the
containing chart is exactly the original embedded smaller chart. -/
theorem isEmbedding_restriction {X : Type v} [TopologicalSpace X]
    (a : IndexedAffinoidAtlas.{u, v, w} K X) (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    IsEmbedding (BanachSpectrum.comap (a.restriction i j h).toBoundedRingHom) := by
  apply (a.isEmbedding_chart j).of_comp_iff.mp
  have heq : a.chart j ∘ BanachSpectrum.comap (a.restriction i j h).toBoundedRingHom =
      a.chart i := funext (a.restriction_chart i j h)
  rw [heq]
  exact a.isEmbedding_chart i

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Full domain representation in a containing original target chart descends
to every smaller admissible original target chart. -/
theorem represents_pullback_of_upper (f : StrongHom A B)
    (i : A.atlas.Index) (j q : B.atlas.Index)
    (hjq : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart q))
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hq : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart q))
    (hrep : PresentedAffinoidAlgebra.Represents K (f.pullback i q hq)
      (f.chartImageLocus i q)) :
    PresentedAffinoidAlgebra.Represents K (f.pullback i j hj)
      (f.chartImageLocus i j) := by
  rw [f.pullback_comp_restriction i j q hjq hj hq] at hrep
  have h := (B.atlas.restriction_represents j q hjq).of_comp_of_injective
    hrep (B.atlas.isEmbedding_restriction j q hjq).injective
  have hlocus : (BanachSpectrum.comap (B.atlas.restriction j q hjq).toBoundedRingHom) ⁻¹'
      f.chartImageLocus i q = f.chartImageLocus i j := by
    ext x
    change B.atlas.chart q
      (BanachSpectrum.comap (B.atlas.restriction j q hjq).toBoundedRingHom x) ∈
        f.baseMap '' Set.range (A.atlas.chart i) ↔
      B.atlas.chart j x ∈ f.baseMap '' Set.range (A.atlas.chart i)
    rw [B.atlas.restriction_chart]
  rw [hlocus] at h
  exact h

/-- Compose full quasi-isomorphisms using actual bounded domain compositions
in common upper charts, then descend to every admissible final chart. -/
theorem IsQuasiIso.compOfDirected {f : StrongHom A B} {g : StrongHom B C}
    (hf : f.IsQuasiIso) (hg : g.IsQuasiIso)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts) :
    (f.compOfDirected g hb hc).IsQuasiIso := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro i k h
  obtain ⟨j, hfij⟩ := f.target_exists i
  obtain ⟨q₀, hgjq₀⟩ := g.target_exists j
  obtain ⟨q, hq₀q, hkq⟩ := hc q₀ k
  have hgjq := hgjq₀.trans hq₀q
  have hq := f.comp_admissible g i j q hfij hgjq
  have hchain := (hg.2 j q hgjq).comp_of_injective (hf.2 i j hfij)
    (hg.isEmbedding_pullback j q hgjq).injective
  have hrep : PresentedAffinoidAlgebra.Represents K
      ((f.compOfDirected g hb hc).pullback i q hq)
      ((f.compOfDirected g hb hc).chartImageLocus i q) := by
    rw [← (f.compOfDirected g hb hc).range_pullback i q hq,
      compOfDirected_pullback f g hb hc i j q hfij hgjq hq,
      hchain.2.1]
    exact hchain
  exact (f.compOfDirected g hb hc).represents_pullback_of_upper i k q hkq h hq hrep

end AffinoidAtlasPresentation.StrongHom

namespace DirectedAtlasPresentation

/-- The actual full strong quasi-isomorphisms in the constructed directed
original-chart category. -/
def quasiIsomorphisms : MorphismProperty (DirectedAtlasPresentation.{u, v, w} K) :=
  fun _ _ f => f.IsQuasiIso

@[simp]
theorem quasiIsomorphisms_iff {A B : DirectedAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) : quasiIsomorphisms f ↔ f.IsQuasiIso := Iff.rfl

instance : (quasiIsomorphisms (K := K)).IsMultiplicative where
  id_mem A := AffinoidAtlasPresentation.StrongHom.isQuasiIso_id A.presentation
  comp_mem {_A B C} _ _ hf hg := hf.compOfDirected hg B.directed C.directed

end DirectedAtlasPresentation

end Langlands.Analytic
