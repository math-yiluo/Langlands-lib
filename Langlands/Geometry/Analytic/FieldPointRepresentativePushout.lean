import Langlands.Geometry.Analytic.FieldPointRepresentativeChartFactorization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout

/-! # Exact pushout pullbacks on faithful local representatives -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.AffinoidAtlasPresentation.FieldPoint

open Set CategoryTheory PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.FaithfulCharacterQuotient

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]
  {P A B C : SaturatedAtlasPresentation.{u, v, v} K}
  (p : FieldPoint L P.presentation) (r : P ⟶ A) (s : P ⟶ B)
  (f : A ⟶ C) (g : B ⟶ C) (h : r ≫ f = s ≫ g)
  (k : P.presentation.atlas.Index) (hk : p.point ∈ range (P.presentation.atlas.chart k))
  (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
  (t : C.presentation.atlas.Index)
  (hr : r.baseMap '' range (P.presentation.atlas.chart k) ⊆
    range (A.presentation.atlas.chart i))
  (hs : s.baseMap '' range (P.presentation.atlas.chart k) ⊆
    range (B.presentation.atlas.chart j))
  (hf : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
    range (C.presentation.atlas.chart t))
  (hg : g.baseMap '' range (B.presentation.atlas.chart j) ⊆
    range (C.presentation.atlas.chart t))

include h in
/-- A commuting strong square gives exact compatible bounded maps from
both target charts into the actual faithful local quotient algebra. -/
theorem chartTestPullback_square :
    (p.chartTestPullback r k hk i hr).comp (f.pullback i t hf) =
      (p.chartTestPullback s k hk j hs).comp (g.pullback j t hg) := by
  have hrf : (r ≫ f).baseMap '' range (P.presentation.atlas.chart k) ⊆
      range (C.presentation.atlas.chart t) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hf ⟨r.baseMap x, hr ⟨x, hx, rfl⟩, rfl⟩
  have hsg : (s ≫ g).baseMap '' range (P.presentation.atlas.chart k) ⊆
      range (C.presentation.atlas.chart t) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨s.baseMap x, hs ⟨x, hx, rfl⟩, rfl⟩
  have he : (r ≫ f).pullback k t hrf = (s ≫ g).pullback k t hsg := by
    simp only [h]
  have hc : (r.pullback k i hr).comp (f.pullback i t hf) =
      (s.pullback k j hs).comp (g.pullback j t hg) :=
    (r.saturatedComp_pullback f P.hasAllLocalDomains A.hasAllLocalDomains
      k i t hr hf hrf).symm.trans
        (he.trans (s.saturatedComp_pullback g P.hasAllLocalDomains B.hasAllLocalDomains
          k j t hs hg hsg))
  apply BoundedAlgHom.ext
  intro a
  exact congrArg (PresentedAffinoidAlgebra.FaithfulCharacterQuotient.map
    (p.boundedEval k hk))
      (congrArg (fun φ : BoundedAlgHom K (C.presentation.atlas.algebra t)
        (P.presentation.atlas.algebra k) => φ a) hc)

/-- The actual affinoid pushout has a bounded map into the faithful local
quotient, obtained from its exact compatible chart pullbacks. -/
def chartTestPushoutPullback :
    BoundedAlgHom K (AffinoidPushout.algebra (f.pullback i t hf) (g.pullback j t hg))
      (algebra (p.boundedEval k hk)) :=
  AffinoidPushout.lift (f.pullback i t hf) (g.pullback j t hg)
    (algebra (p.boundedEval k hk))
    (p.chartTestPullback r k hk i hr) (p.chartTestPullback s k hk j hs)
    (p.chartTestPullback_square r s f g h k hk i j t hr hs hf hg)

/-- The first original quotient leg recovers exactly the first direct
representative-chart bounded pullback. -/
theorem chartTestPushoutPullback_comp_leftMap :
    (p.chartTestPushoutPullback r s f g h k hk i j t hr hs hf hg).comp
      (AffinoidPushout.leftMap (f.pullback i t hf) (g.pullback j t hg)) =
        p.chartTestPullback r k hk i hr :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

/-- The second original quotient leg recovers exactly the second direct
representative-chart bounded pullback. -/
theorem chartTestPushoutPullback_comp_rightMap :
    (p.chartTestPushoutPullback r s f g h k hk i j t hr hs hf hg).comp
      (AffinoidPushout.rightMap (f.pullback i t hf) (g.pullback j t hg)) =
        p.chartTestPullback s k hk j hs :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

/-- The exact two bounded projection pullbacks determine this map uniquely. -/
theorem chartTestPushoutPullback_unique
    (ψ : BoundedAlgHom K
      (AffinoidPushout.algebra (f.pullback i t hf) (g.pullback j t hg))
      (algebra (p.boundedEval k hk)))
    (hl : ψ.comp (AffinoidPushout.leftMap (f.pullback i t hf) (g.pullback j t hg)) =
      p.chartTestPullback r k hk i hr)
    (hr' : ψ.comp (AffinoidPushout.rightMap (f.pullback i t hf) (g.pullback j t hg)) =
      p.chartTestPullback s k hk j hs) :
    ψ = p.chartTestPushoutPullback r s f g h k hk i j t hr hs hf hg :=
  AffinoidPushout.hom_ext _ _ _
    ψ (p.chartTestPushoutPullback r s f g h k hk i j t hr hs hf hg)
    (hl.trans (p.chartTestPushoutPullback_comp_leftMap r s f g h
      k hk i j t hr hs hf hg).symm)
    (hr'.trans (p.chartTestPushoutPullback_comp_rightMap r s f g h
      k hk i j t hr hs hf hg).symm)

end Langlands.Analytic.AffinoidAtlasPresentation.FieldPoint
