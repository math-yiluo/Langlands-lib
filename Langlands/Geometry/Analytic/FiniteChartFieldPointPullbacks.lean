import Langlands.Geometry.Analytic.FieldPointRepresentativePointPushout
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Statement

/-! # Full field-point lifting over finite original chart pairs -/

noncomputable section

universe u v uL

namespace Langlands.Analytic

open Set CategoryTheory Limits PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

namespace SaturatedAtlasPresentation

variable {P A B X : SaturatedAtlasPresentation.{u, v, v} K}

/-- Compute the actual descended functor on the image of a strong map. -/
theorem localizedFieldPointFunctor_map_strong (f : A ⟶ B)
    (p : FieldPoint L A.presentation) :
    (localizedFieldPointFunctor L).map (localizationFunctor.map f) p =
      p.map f A.hasAllLocalDomains := by
  rfl

/-- A localized commuting square gives equality of the entire iterated
field-point images, even when the original strong square is not supplied. -/
theorem fieldPoint_map_square
    (r : P ⟶ A) (s : P ⟶ B) (f : A ⟶ X) (g : B ⟶ X)
    (h : localizationFunctor.map r ≫ localizationFunctor.map f =
      localizationFunctor.map s ≫ localizationFunctor.map g)
    (p : FieldPoint L P.presentation) :
    (p.map r P.hasAllLocalDomains).map f A.hasAllLocalDomains =
      (p.map s P.hasAllLocalDomains).map g B.hasAllLocalDomains := by
  have he := congrArg (fun e : localizationFunctor.obj P ⟶ localizationFunctor.obj X =>
    (localizedFieldPointFunctor L).map e p) h
  simp only [Functor.map_comp] at he
  exact he

/-- The original chart-pair condition needed for full field-point lifting.
Its finite Banach leg controls the size of the actual affinoid pushout. -/
def HasFiniteChartPairs (f : A ⟶ X) (g : B ⟶ X) : Prop :=
  ∀ (a : A.presentation.space) (b : B.presentation.space),
    f.baseMap a = g.baseMap b →
    ∃ (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
      (t : X.presentation.atlas.Index)
      (hf : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
        range (X.presentation.atlas.chart t))
      (_hg : g.baseMap '' range (B.presentation.atlas.chart j) ⊆
        range (X.presentation.atlas.chart t)),
      a ∈ range (A.presentation.atlas.chart i) ∧
      b ∈ range (B.presentation.atlas.chart j) ∧
      (f.pullback i t hf).IsFiniteBanach

end SaturatedAtlasPresentation

namespace AffinoidAtlasPresentation.FieldPoint

variable {A B X : SaturatedAtlasPresentation.{u, v, v} K}

/-- Full compatibility gives compatibility of the actual original bounded
evaluations on every admissible chosen chart pair. -/
theorem boundedEval_comp_pullback_eq
    (a : FieldPoint L A.presentation) (b : FieldPoint L B.presentation)
    (f : A ⟶ X) (g : B ⟶ X)
    (hab : a.map f A.hasAllLocalDomains = b.map g B.hasAllLocalDomains)
    (i : A.presentation.atlas.Index)
    (hi : a.point ∈ range (A.presentation.atlas.chart i))
    (j : B.presentation.atlas.Index)
    (hj : b.point ∈ range (B.presentation.atlas.chart j))
    (t : X.presentation.atlas.Index)
    (hf : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (X.presentation.atlas.chart t))
    (hg : g.baseMap '' range (B.presentation.atlas.chart j) ⊆
      range (X.presentation.atlas.chart t)) :
    (a.boundedEval i hi).comp (f.pullback i t hf) =
      (b.boundedEval j hj).comp (g.pullback j t hg) := by
  have he : (a.map f A.hasAllLocalDomains).boundedEval t (hf ⟨a.point, hi, rfl⟩) =
      (b.map g B.hasAllLocalDomains).boundedEval t (hg ⟨b.point, hj, rfl⟩) := by
    exact BoundedAlgHom.ext (AlgHom.congr_fun
      (FieldPoint.eval_congr hab t (hf ⟨a.point, hi, rfl⟩) (hg ⟨b.point, hj, rfl⟩)))
  exact (a.map_boundedEval f A.hasAllLocalDomains t _ i hi hf).symm.trans
    (he.trans (b.map_boundedEval g B.hasAllLocalDomains t _ j hj hg))

end AffinoidAtlasPresentation.FieldPoint

namespace SmallAffinoidSpectrum

variable (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)]
  {A B : SaturatedAtlasPresentation.{u, v, v} K}

omit [CompleteSpace K] in
private theorem transport_comp
    {R' S T : PresentedAffinoidAlgebra K} (h : R' = R)
    (φ : BoundedAlgHom K S R) (ψ : BoundedAlgHom K T S) :
    (h.symm ▸ φ).comp ψ = h.symm ▸ (φ.comp ψ) := by
  subst R
  rfl

/-- Composition of a small-spectrum chart map retains the actual original
bounded composite on every admissible intermediate chart. -/
theorem chartMap_comp
    (i : A.presentation.atlas.Index)
    (φ : BoundedAlgHom K (A.presentation.atlas.algebra i) R)
    (f : A ⟶ B) (j : B.presentation.atlas.Index)
    (hf : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart j)) :
    chartMap R i φ ≫ f = chartMap R j (φ.comp (f.pullback i j hf)) := by
  change SaturatedAtlasPresentation.chartSourceMap
      (globalIndex R) (globalRange R) i ((globalAlgebra R).symm ▸ φ) ≫ f = _
  rw [SaturatedAtlasPresentation.chartSourceMap_comp _ _ _ _ f j hf]
  exact congrArg (SaturatedAtlasPresentation.chartSourceMap
    (globalIndex R) (globalRange R) j)
      (transport_comp R (globalAlgebra R) φ (f.pullback i j hf))

/-- Every point of a small-spectrum chart map lies in its selected chart. -/
theorem chartMap_mem (i : A.presentation.atlas.Index)
    (φ : BoundedAlgHom K (A.presentation.atlas.algebra i) R)
    (x : (saturated.{u, v} R).presentation.space) :
    (chartMap R i φ).baseMap x ∈ range (A.presentation.atlas.chart i) :=
  chartMap_admissible R i φ (globalIndex R)
    ⟨x, (globalRange R).symm ▸ mem_univ x, rfl⟩

end SmallAffinoidSpectrum

namespace SaturatedAtlasPresentation

variable [CompleteSpace L] [IsUltrametricDist L]
  {P A B X : SaturatedAtlasPresentation.{u, v, v} K}

set_option maxHeartbeats 1200000 in
/-- A compatible pair of full points has a unique lift to any supplied localized
pullback when its containing chart pair has an actual small pushout spectrum. -/
theorem existsUnique_fieldPoint_lift_of_small_pair
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (r : P ⟶ A) (s : P ⟶ B) (f : A ⟶ X) (g : B ⟶ X)
    (hP : IsPullback (localizationFunctor.map r) (localizationFunctor.map s)
      (localizationFunctor.map f) (localizationFunctor.map g))
    (a : FieldPoint L A.presentation) (b : FieldPoint L B.presentation)
    (hab : a.map f A.hasAllLocalDomains = b.map g B.hasAllLocalDomains)
    (i : A.presentation.atlas.Index) (hi : a.point ∈ range (A.presentation.atlas.chart i))
    (j : B.presentation.atlas.Index) (hj : b.point ∈ range (B.presentation.atlas.chart j))
    (t : X.presentation.atlas.Index)
    (hf : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (X.presentation.atlas.chart t))
    (hg : g.baseMap '' range (B.presentation.atlas.chart j) ⊆
      range (X.presentation.atlas.chart t))
    [Small.{v} (BanachSpectrum (AffinoidPushout.algebra
      (f.pullback i t hf) (g.pullback j t hg)))] :
    ∃! p : FieldPoint L P.presentation,
      p.map r P.hasAllLocalDomains = a ∧ p.map s P.hasAllLocalDomains = b := by
  let F₀ := f.pullback i t hf
  let G₀ := g.pullback j t hg
  let D := AffinoidPushout.algebra F₀ G₀
  let Z := SmallAffinoidSpectrum.saturated.{u, v} D
  let c := AffinoidPushout.lift F₀ G₀ L (a.boundedEval i hi) (b.boundedEval j hj)
    (a.boundedEval_comp_pullback_eq b f g hab i hi j hj t hf hg)
  let z := SmallAffinoidSpectrum.fieldPoint D hd c
  let l : Z ⟶ A := SmallAffinoidSpectrum.chartMap D i (AffinoidPushout.leftMap F₀ G₀)
  let m : Z ⟶ B := SmallAffinoidSpectrum.chartMap D j (AffinoidPushout.rightMap F₀ G₀)
  have hc : l ≫ f = m ≫ g := by
    dsimp only [l, m]
    rw [SmallAffinoidSpectrum.chartMap_comp D i _ f t hf,
      SmallAffinoidSpectrum.chartMap_comp D j _ g t hg,
      AffinoidPushout.condition]
  have hl : z.map l Z.hasAllLocalDomains = a :=
    SmallAffinoidSpectrum.fieldPoint_chartMap D hd c a i hi _
      (AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _)
  have hm : z.map m Z.hasAllLocalDomains = b :=
    SmallAffinoidSpectrum.fieldPoint_chartMap D hd c b j hj _
      (AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _)
  let Q := localizationFunctor (K := K)
  let E := localizedFieldPointFunctor (K := K) L
  have hQc : Q.map l ≫ Q.map f = Q.map m ≫ Q.map g := by
    simpa only [← Functor.map_comp] using congrArg (fun e : Z ⟶ X => Q.map e) hc
  let n := hP.lift (Q.map l) (Q.map m) hQc
  refine ⟨E.map n z, ⟨?_, ?_⟩, ?_⟩
  · have he := congrArg (fun e : Q.obj Z ⟶ Q.obj A => E.map e z)
      (hP.lift_fst (Q.map l) (Q.map m) hQc)
    simp only [Functor.map_comp] at he
    change (E.map n z).map r P.hasAllLocalDomains = z.map l Z.hasAllLocalDomains at he
    exact he.trans hl
  · have he := congrArg (fun e : Q.obj Z ⟶ Q.obj B => E.map e z)
      (hP.lift_snd (Q.map l) (Q.map m) hQc)
    simp only [Functor.map_comp] at he
    change (E.map n z).map s P.hasAllLocalDomains = z.map m Z.hasAllLocalDomains at he
    exact he.trans hm
  · intro p hp
    have hri : r.baseMap p.point ∈ range (A.presentation.atlas.chart i) := by
      change (p.map r P.hasAllLocalDomains).point ∈ _
      rw [hp.1]
      exact hi
    have hsj : s.baseMap p.point ∈ range (B.presentation.atlas.chart j) := by
      change (p.map s P.hasAllLocalDomains).point ∈ _
      rw [hp.2]
      exact hj
    obtain ⟨k, hk, hr, hs, _⟩ := p.exists_chartTest_pair_factorization hd r s i hri j hsj
    let : Small.{v} (BanachSpectrum (P.presentation.atlas.algebra k)) :=
      small_of_injective (P.presentation.atlas.isEmbedding_chart k).injective
    let χ := p.boundedEval k hk
    let := FaithfulCharacterQuotient.small_spectrum.{u, v} χ
    have hpoint := fieldPoint_map_square r s f g hP.w p
    let ρ := p.chartTestPushoutPullbackOfPointMapEq r s f g hpoint k hk i j t hr hs hf hg
    let δ : p.chartTestSource k hk ⟶ Z := SmallAffinoidSpectrum.map ρ
    have hchar : (FaithfulCharacterQuotient.character χ).comp ρ = c := by
      apply AffinoidPushout.hom_ext F₀ G₀ L
      · change (FaithfulCharacterQuotient.character χ).comp
          (ρ.comp (AffinoidPushout.leftMap F₀ G₀)) = _
        rw [p.chartTestPushoutPullbackOfPointMapEq_comp_leftMap,
          p.character_comp_chartTestPullback, AffinoidPushout.lift_comp_leftMap]
        exact BoundedAlgHom.ext (AlgHom.congr_fun
          (FieldPoint.eval_congr hp.1 i (hr ⟨p.point, hk, rfl⟩) hi))
      · change (FaithfulCharacterQuotient.character χ).comp
          (ρ.comp (AffinoidPushout.rightMap F₀ G₀)) = _
        rw [p.chartTestPushoutPullbackOfPointMapEq_comp_rightMap,
          p.character_comp_chartTestPullback, AffinoidPushout.lift_comp_rightMap]
        exact BoundedAlgHom.ext (AlgHom.congr_fun
          (FieldPoint.eval_congr hp.2 j (hs ⟨p.point, hk, rfl⟩) hj))
    have hδ : (p.chartTestPoint hd k hk).map δ
        (p.chartTestSource k hk).hasAllLocalDomains = z := by
      change (SmallAffinoidSpectrum.fieldPoint (FaithfulCharacterQuotient.algebra χ)
        hd (FaithfulCharacterQuotient.character χ)).map (SmallAffinoidSpectrum.map ρ) _ =
          SmallAffinoidSpectrum.fieldPoint D hd c
      rw [SmallAffinoidSpectrum.fieldPoint_map, hchar]
    have hδl : δ ≫ l = p.chartTestMap k hk ≫ r := by
      apply FaithfulCharacterQuotient.hom_eq_of_common_chart_testPoint_map_eq χ hd _ _ i
      · intro x
        exact SmallAffinoidSpectrum.chartMap_mem D i _ (δ.baseMap x)
      · intro x
        exact hr ⟨(p.chartTestMap k hk).baseMap x, p.chartTestMap_mem k hk x, rfl⟩
      · change (p.chartTestPoint hd k hk).map (δ.saturatedComp l _ _) _ =
          (p.chartTestPoint hd k hk).map ((p.chartTestMap k hk).saturatedComp r _ _) _
        rw [FieldPoint.map_saturatedComp, FieldPoint.map_saturatedComp,
          hδ, hl, p.chartTestPoint_map, hp.1]
    have hδm : δ ≫ m = p.chartTestMap k hk ≫ s := by
      apply FaithfulCharacterQuotient.hom_eq_of_common_chart_testPoint_map_eq χ hd _ _ j
      · intro x
        exact SmallAffinoidSpectrum.chartMap_mem D j _ (δ.baseMap x)
      · intro x
        exact hs ⟨(p.chartTestMap k hk).baseMap x, p.chartTestMap_mem k hk x, rfl⟩
      · change (p.chartTestPoint hd k hk).map (δ.saturatedComp m _ _) _ =
          (p.chartTestPoint hd k hk).map ((p.chartTestMap k hk).saturatedComp s _ _) _
        rw [FieldPoint.map_saturatedComp, FieldPoint.map_saturatedComp,
          hδ, hm, p.chartTestPoint_map, hp.2]
    have hrep : Q.map (p.chartTestMap k hk) = Q.map δ ≫ n := by
      apply hP.hom_ext
      · rw [Category.assoc, hP.lift_fst (Q.map l) (Q.map m) hQc,
          ← Q.map_comp, ← Q.map_comp, hδl]
      · rw [Category.assoc, hP.lift_snd (Q.map l) (Q.map m) hQc,
          ← Q.map_comp, ← Q.map_comp, hδm]
    have he := congrArg
      (fun e : Q.obj (p.chartTestSource k hk) ⟶ Q.obj P =>
        E.map e (p.chartTestPoint hd k hk)) hrep
    simp only [Functor.map_comp] at he
    change (p.chartTestPoint hd k hk).map (p.chartTestMap k hk) _ =
      E.map n ((p.chartTestPoint hd k hk).map δ _) at he
    rw [p.chartTestPoint_map] at he
    exact he.trans (congrArg (fun z' : FieldPoint L Z.presentation => E.map n z') hδ)

/-- Finite Banach base change supplies the smallness needed for a unique full
field-point lift over each compatible pair of ordinary chart neighborhoods. -/
theorem existsUnique_fieldPoint_lift_of_finiteChartPairs
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (r : P ⟶ A) (s : P ⟶ B) (f : A ⟶ X) (g : B ⟶ X)
    (hP : IsPullback (localizationFunctor.map r) (localizationFunctor.map s)
      (localizationFunctor.map f) (localizationFunctor.map g))
    (hcharts : HasFiniteChartPairs f g)
    (a : FieldPoint L A.presentation) (b : FieldPoint L B.presentation)
    (hab : a.map f A.hasAllLocalDomains = b.map g B.hasAllLocalDomains) :
    ∃! p : FieldPoint L P.presentation,
      p.map r P.hasAllLocalDomains = a ∧ p.map s P.hasAllLocalDomains = b := by
  obtain ⟨i, j, t, hf, hg, hi, hj, hfinite⟩ :=
    hcharts a.point b.point (congrArg FieldPoint.point hab)
  let : Small.{v} (BanachSpectrum (B.presentation.atlas.algebra j)) :=
    small_of_injective (B.presentation.atlas.isEmbedding_chart j).injective
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout
    (f.pullback i t hf) (g.pullback j t hg) hpush hfinite
  exact existsUnique_fieldPoint_lift_of_small_pair hd r s f g hP a b hab i hi j hj t hf hg

/-- The actual descended full field-point functor preserves a supplied
localized strong square whenever its cospan has finite original chart pairs. -/
theorem fieldPoint_isPullback_of_finiteChartPairs
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (r : P ⟶ A) (s : P ⟶ B) (f : A ⟶ X) (g : B ⟶ X)
    (hP : IsPullback (localizationFunctor.map r) (localizationFunctor.map s)
      (localizationFunctor.map f) (localizationFunctor.map g))
    (hcharts : HasFiniteChartPairs f g) :
    IsPullback ((localizedFieldPointFunctor L).map (localizationFunctor.map r))
      ((localizedFieldPointFunctor L).map (localizationFunctor.map s))
      ((localizedFieldPointFunctor L).map (localizationFunctor.map f))
      ((localizedFieldPointFunctor L).map (localizationFunctor.map g)) := by
  let E := localizedFieldPointFunctor (K := K) L
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
  · exact (E.map_comp _ _).symm.trans
      ((congrArg E.map hP.w).trans (E.map_comp _ _))
  · intro p q hpq
    change p.map r P.hasAllLocalDomains = q.map r P.hasAllLocalDomains ∧
      p.map s P.hasAllLocalDomains = q.map s P.hasAllLocalDomains at hpq
    obtain ⟨z, _, hu⟩ := existsUnique_fieldPoint_lift_of_finiteChartPairs
      hd hpush r s f g hP hcharts (p.map r P.hasAllLocalDomains)
      (p.map s P.hasAllLocalDomains) (fieldPoint_map_square r s f g hP.w p)
    exact (hu p ⟨rfl, rfl⟩).trans (hu q ⟨hpq.1.symm, hpq.2.symm⟩).symm
  · intro a b hab
    exact (existsUnique_fieldPoint_lift_of_finiteChartPairs
      hd hpush r s f g hP hcharts a b hab).exists

end SaturatedAtlasPresentation

end Langlands.Analytic
