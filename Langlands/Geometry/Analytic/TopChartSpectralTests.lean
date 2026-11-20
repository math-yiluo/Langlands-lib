import Langlands.Geometry.Analytic.AffineTopChartPullbacks
import Langlands.Geometry.Analytic.ContinuousAnalyticAction
import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.Geometry.Analytic.QuotientTopTargetHom
import Langlands.Geometry.Analytic.StrictTestDomain.SpectralDisplacement

/-! # Localized tests on greatest charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set BanachSpectrum AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- A morphism into a greatest-chart presentation has a unique strong
representative on its original source. -/
def localizedTopTargetHomEquiv (j : B.presentation.atlas.Index)
    (hj : ∀ i, range (B.presentation.atlas.chart i) ⊆ range (B.presentation.atlas.chart j)) :
    (A ⟶ B) ≃ (localizationFunctor.obj A ⟶ localizationFunctor.obj B) :=
  (SourceCategory.topTargetHomEquiv j hj).trans sourceHomEquiv

@[simp]
theorem localizedTopTargetHomEquiv_apply (j : B.presentation.atlas.Index)
    (hj : ∀ i, range (B.presentation.atlas.chart i) ⊆ range (B.presentation.atlas.chart j))
    (φ : A ⟶ B) : localizedTopTargetHomEquiv j hj φ = localizationFunctor.map φ :=
  sourceHomEquiv.apply_symm_apply _

theorem range_greatestChart_eq_univ (i : A.presentation.atlas.Index)
    (hi : ∀ k, range (A.presentation.atlas.chart k) ⊆ range (A.presentation.atlas.chart i)) :
    range (A.presentation.atlas.chart i) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨k, hk⟩ := A.presentation.atlas.exists_mem_range_chart x
  exact hi k hk

variable (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
  (hi : ∀ k, range (A.presentation.atlas.chart k) ⊆ range (A.presentation.atlas.chart i))
  (hj : ∀ k, range (B.presentation.atlas.chart k) ⊆ range (B.presentation.atlas.chart j))
  (a b : A ⟶ B) (f : B.presentation.atlas.algebra j) {ε : ℝ} (hε : 0 < ε)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hi in
/-- On greatest charts the localized test is precisely the spectral bound
on the difference of the recovered bounded pullbacks. -/
theorem isNear_greatestChart_iff :
    IsNear (X := localizationFunctor.obj B)
        (⟨j, f, ε, hε⟩ : TestTriple B) (localizationFunctor.map a) (localizationFunctor.map b) ↔
      SpectralBound (a.pullbackAtTop j hj i f - b.pullbackAtTop j hj i f) ε := by
  let τ : TestTriple B := ⟨j, f, ε, hε⟩
  constructor
  · intro hnear x
    obtain ⟨T, s, hs, a', b', ha', hb', hstrong⟩ := hnear
    change T ⟶ A at s
    change T ⟶ B at a' b'
    change StrongNear τ a' b' at hstrong
    have lift_eq (c : A ⟶ B) (c' : T ⟶ B)
        (hc : localizationFunctor.map c =
          (localizedQuasiIso s hs).inv ≫ localizationFunctor.map c') :
        s ≫ c = c' := by
      apply (localizedTopTargetHomEquiv j hj).injective
      simp only [localizedTopTargetHomEquiv_apply]
      rw [Functor.map_comp]
      exact (congrArg (localizationFunctor.map s ≫ ·) hc).trans
        (localizationFunctor_map_s_comp_localizedRightFraction
          (MorphismProperty.RightFraction.mk s hs c'))
    have ha : s ≫ a = a' := lift_eq a a' ha'
    have hb : s ≫ b = b' := lift_eq b b' hb'
    obtain ⟨k, y, hy⟩ := T.presentation.atlas.exists_mem_range_chart
      (hs.inverseBaseMap (A.presentation.atlas.chart i x))
    have htest : IsTestPiece τ a' b' k :=
      ⟨a'.image_chart_top j hj k, b'.image_chart_top j hj k⟩
    have hbound : y (a'.pullbackAtTop j hj k f - b'.pullbackAtTop j hj k f) ≤ ε :=
      hstrong.2.2 k htest y
    rw [← ha, ← hb, pullbackAtTop_comp s a i j hi hj,
      pullbackAtTop_comp s b i j hi hj] at hbound
    let r := s.pullbackAtTop i hi k
    have hxy : comap r.toBoundedRingHom y = x := by
      apply (A.presentation.atlas.isEmbedding_chart i).injective
      exact (s.chart_comm k i (s.image_chart_top i hi k) y).trans
        ((congrArg s.baseMap hy).trans (hs.baseMap_inverseBaseMap _))
    change y (r (a.pullbackAtTop j hj i f) - r (b.pullbackAtTop j hj i f)) ≤ ε at hbound
    rw [← map_sub] at hbound
    change comap r.toBoundedRingHom y
      (a.pullbackAtTop j hj i f - b.pullbackAtTop j hj i f) ≤ ε at hbound
    simpa only [hxy] using hbound
  · intro hbound
    apply isNear_localizationFunctor_map (X := localizationFunctor.obj B) (τ := τ)
    change StrongNear τ a b
    have hτ : τ.locus = univ := range_greatestChart_eq_univ j hj
    refine ⟨by simp only [hτ, preimage_univ], ?_, ?_⟩
    · intro x hx
      exact ⟨i, ⟨a.image_chart_top j hj i, b.image_chart_top j hj i⟩,
        (range_greatestChart_eq_univ i hi).symm ▸ mem_univ x⟩
    · intro k hk y
      change y (a.pullbackAtTop j hj k f - b.pullbackAtTop j hj k f) ≤ ε
      rw [← a.restriction_comp_pullbackAtTop j hj k i (hi k),
        ← b.restriction_comp_pullbackAtTop j hj k i (hi k)]
      let r := A.presentation.atlas.restriction k i (hi k)
      change y (r (a.pullbackAtTop j hj i f) - r (b.pullbackAtTop j hj i f)) ≤ ε
      rw [← map_sub]
      exact hbound (comap r.toBoundedRingHom y)

end Langlands.Analytic.SaturatedAtlasPresentation
