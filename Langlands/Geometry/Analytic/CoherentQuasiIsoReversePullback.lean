import Langlands.Geometry.Analytic.StrongQuasiIsoDomainImage
import Langlands.Geometry.Analytic.AtlasSaturationComparison

/-! # Actual reverse chart pullbacks without directedness -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A B} (hf : f.IsQuasiIso)

/-- Containment in a full chart image constructs an actual local-domain
inclusion, with its complete bounded restriction. -/
def reverseChartInclusion (j : B.atlas.Index) (i : A.atlas.Index)
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i)) :
    B.atlas.originalLocalDomain j ⟶ hf.domainImage (A.atlas.originalLocalDomain i) :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [hf.domainImage_locus, A.atlas.originalLocalDomain_locus,
      B.atlas.originalLocalDomain_locus]
    exact h)

/-- This map uses the original presented chart algebras. Neither directedness
nor a global reverse strong map is an input. -/
def reverseChartPullback (j : B.atlas.Index) (i : A.atlas.Index)
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i)) :
    BoundedAlgHom K (A.atlas.algebra i) (B.atlas.algebra j) :=
  (hf.reverseChartInclusion j i h).restriction

/-- The spectrum equation comes from the actual inclusion's ambient square. -/
theorem reverseChartPullback_chart (j : B.atlas.Index) (i : A.atlas.Index)
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i))
    (x : BanachSpectrum (B.atlas.algebra j)) :
    f.baseMap (A.atlas.chart i
      (BanachSpectrum.comap (hf.reverseChartPullback j i h).toBoundedRingHom x)) =
        B.atlas.chart j x := by
  let y : BanachSpectrum (A.atlas.algebra i) :=
    BanachSpectrum.comap (hf.reverseChartPullback j i h).toBoundedRingHom x
  calc
    f.baseMap (A.atlas.chart i y) =
        f.baseMap ((A.atlas.originalLocalDomain i).ambientMap y) :=
      congrArg f.baseMap (A.atlas.originalLocalDomain_ambientMap i y).symm
    _ = (hf.domainImage (A.atlas.originalLocalDomain i)).ambientMap y :=
      (hf.domainImage_ambientMap (A.atlas.originalLocalDomain i) y).symm
    _ = (B.atlas.originalLocalDomain j).ambientMap x :=
      (hf.reverseChartInclusion j i h).ambientMap_naturality x
    _ = B.atlas.chart j x := B.atlas.originalLocalDomain_ambientMap j x

/-- Full representation is inherited from the actual inclusion, on every
presented-affinoid coefficient test, not merely on spectrum points. -/
theorem reverseChartPullback_represents (j : B.atlas.Index) (i : A.atlas.Index)
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i)) :
    Represents K (hf.reverseChartPullback j i h)
      ((fun x : BanachSpectrum (A.atlas.algebra i) => f.baseMap (A.atlas.chart i x)) ⁻¹'
        Set.range (B.atlas.chart j)) := by
  have hrep := (hf.reverseChartInclusion j i h).represents
  have heq :
      (hf.domainImage (A.atlas.originalLocalDomain i)).ambientMap ⁻¹'
          (B.atlas.originalLocalDomain j).locus =
        (fun x : BanachSpectrum (A.atlas.algebra i) => f.baseMap (A.atlas.chart i x)) ⁻¹'
          Set.range (B.atlas.chart j) := by
    have hm :
        (fun x : BanachSpectrum (A.atlas.algebra i) =>
          (hf.domainImage (A.atlas.originalLocalDomain i)).ambientMap x) =
        (fun x => f.baseMap (A.atlas.chart i x)) := by
      funext x
      exact (hf.domainImage_ambientMap (A.atlas.originalLocalDomain i) x).trans
        (congrArg f.baseMap (A.atlas.originalLocalDomain_ambientMap i x))
    exact congrArg₂
      (fun (g : BanachSpectrum (A.atlas.algebra i) → B.space) (S : Set B.space) =>
        g ⁻¹' S) hm (B.atlas.originalLocalDomain_locus j)
  exact heq ▸ hrep

/-- Intrinsic coherence makes both routes through arbitrary original source
and target restrictions equal as entire bounded algebra maps. -/
theorem reverseChartPullback_naturality (hc : f.HasCoherentPullbacks)
    (j j' : B.atlas.Index) (i i' : A.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i))
    (h' : Set.range (B.atlas.chart j') ⊆ f.baseMap '' Set.range (A.atlas.chart i')) :
    (B.atlas.restriction j j' hj).comp (hf.reverseChartPullback j' i' h') =
      (hf.reverseChartPullback j i h).comp (A.atlas.restriction i i' hi) := by
  let p : B.atlas.originalLocalDomain j ⟶ B.atlas.originalLocalDomain j' :=
    LocalDomain.Inclusion.ofSubset _ _ (by
      rw [B.atlas.originalLocalDomain_locus, B.atlas.originalLocalDomain_locus]
      exact hj)
  let q : A.atlas.originalLocalDomain i ⟶ A.atlas.originalLocalDomain i' :=
    LocalDomain.Inclusion.ofSubset _ _ (by
      rw [A.atlas.originalLocalDomain_locus, A.atlas.originalLocalDomain_locus]
      exact hi)
  have heq := congrArg LocalDomain.Inclusion.restriction
    (@Subsingleton.elim (LocalDomain.Inclusion (B.atlas.originalLocalDomain j)
      (hf.domainImage (A.atlas.originalLocalDomain i'))) inferInstance
        (p ≫ hf.reverseChartInclusion j' i' h')
        (hf.reverseChartInclusion j i h ≫ hf.domainImageMap hc q))
  rw [LocalDomain.Inclusion.restriction_comp, LocalDomain.Inclusion.restriction_comp,
    hf.domainImageMap_restriction,
    B.atlas.originalLocalDomain_restriction j j' hj p,
    A.atlas.originalLocalDomain_restriction i i' hi q] at heq
  exact heq

/-- Every containing target chart gives the full forward/reverse
factorization equation, without finding a common upper chart. -/
theorem reverseChartPullback_comp_pullback (hc : f.HasCoherentPullbacks)
    (j : B.atlas.Index) (i : A.atlas.Index)
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i))
    (q : B.atlas.Index)
    (hfq : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart q))
    (hjq : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart q)) :
    (hf.reverseChartPullback j i h).comp (f.pullback i q hfq) =
      B.atlas.restriction j q hjq := by
  let U := A.atlas.originalLocalDomain i
  have hU : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart q) := by
    rw [A.atlas.originalLocalDomain_locus]
    exact hfq
  have hD : (hf.domainImage U).locus ⊆ Set.range (B.atlas.chart q) := by
    rw [hf.domainImage_locus]
    exact hU
  have hJ : (B.atlas.originalLocalDomain j).locus ⊆ Set.range (B.atlas.chart q) := by
    rw [B.atlas.originalLocalDomain_locus]
    exact hjq
  have heq := (hf.reverseChartInclusion j i h).comp_chart q hJ hD
  rw [hf.domainImage_chartRestriction U q hD hU,
    f.localChartPullback_of_parent_admissible hc U q hfq hU] at heq
  change (hf.reverseChartPullback j i h).comp (f.pullback i q hfq) =
    B.atlas.domainChartRestriction j q (Domain.whole K (B.atlas.algebra j)) hJ at heq
  exact heq.trans (B.atlas.domainChartRestriction_of_chartSubset j q
    (Domain.whole K (B.atlas.algebra j)) hJ hjq)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso
