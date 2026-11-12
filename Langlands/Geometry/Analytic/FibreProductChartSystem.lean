import Langlands.Geometry.Analytic.CompatibleStrongMaps
import Langlands.Geometry.Analytic.AffinoidProductChartSystem
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange

/-! # The chart system of a fibre product of analytic spaces -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra

/-- A bounded map whose spectrum image lies in the locus of a domain and which has the
universal factorization property for that locus represents the locus. -/
theorem represents_of_universal {B A : PresentedAffinoidAlgebra K} (i : BoundedAlgHom K B A)
    (D : Domain K B) (himg : HasImageIn K i D.locus)
    (huniv : ∀ (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K B R),
      HasImageIn K φ D.locus → ∃! ψ : BoundedAlgHom K A R, ψ.comp i = φ) :
    Represents K i D.locus := by
  refine ⟨D.represents.1, subset_antisymm ?_ ?_, huniv⟩
  · rintro _ ⟨x, rfl⟩
    exact himg x
  · intro y hy
    rw [← D.represents.2.1] at hy
    obtain ⟨z, rfl⟩ := hy
    have hD : HasImageIn K D.baseMap D.locus := fun x => by
      rw [← D.represents.2.1]
      exact ⟨x, rfl⟩
    obtain ⟨θ, hθ, -⟩ := huniv D.algebra D.baseMap hD
    refine ⟨BanachSpectrum.comap θ.toBoundedRingHom z, ?_⟩
    change BanachSpectrum.comap (θ.comp i).toBoundedRingHom z = _
    rw [hθ]

end PresentedAffinoidAlgebra

namespace FibreProduct

open AffinoidAtlasPresentation

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-! ## Common base charts -/

/-- A chart `k` of the base containing the images of the charts `i` and `j`. -/
def IsCommonBase (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index) : Prop :=
  f.baseMap '' range (A.atlas.chart i) ⊆ range (C.atlas.chart k) ∧
    g.baseMap '' range (B.atlas.chart j) ⊆ range (C.atlas.chart k)

variable {f g}

/-- The pushout condition over one common base chart implies it over every other one. -/
theorem condition_of_isCommonBase {i : A.atlas.Index} {j : B.atlas.Index}
    {k k' : C.atlas.Index} (hk : IsCommonBase f g i j k) (hk' : IsCommonBase f g i j k')
    {T : PresentedAffinoidAlgebra K} (α : BoundedAlgHom K (A.atlas.algebra i) T)
    (β : BoundedAlgHom K (B.atlas.algebra j) T)
    (h : α.comp (f.pullback i k hk.1) = β.comp (g.pullback j k hk.2)) :
    α.comp (f.pullback i k' hk'.1) = β.comp (g.pullback j k' hk'.2) := by
  have hα := (f.coherent i k k' hk.1 hk'.1).comp C.atlas α
  have hβ := (g.coherent j k k' hk.2 hk'.2).comp C.atlas β
  rw [h] at hα
  have himg : ∀ x : BanachSpectrum T, C.atlas.chart k
      (BanachSpectrum.comap (β.comp (g.pullback j k hk.2)).toBoundedRingHom x) ∈
        range (C.atlas.chart k') := by
    intro x
    change C.atlas.chart k (BanachSpectrum.comap (g.pullback j k hk.2).toBoundedRingHom
      (BanachSpectrum.comap β.toBoundedRingHom x)) ∈ _
    rw [g.chart_comm]
    exact hk'.2 ⟨_, ⟨_, rfl⟩, rfl⟩
  exact (C.atlas.eq_changeMapChart k k' T _ himg _ hα).trans
    (C.atlas.eq_changeMapChart k k' T _ himg _ hβ).symm

variable (f g)

/-- Pairs of charts whose images lie in a common base chart. -/
def PairIndex : Type w :=
  {p : A.atlas.Index × B.atlas.Index // ∃ k, IsCommonBase f g p.1 p.2 k}

/-- The chosen common base chart of a pair. -/
def base (p : PairIndex f g) : C.atlas.Index := p.2.choose

theorem isCommonBase_base (p : PairIndex f g) : IsCommonBase f g p.1.1 p.1.2 (base f g p) :=
  p.2.choose_spec

/-- The pullback from the chosen base chart to the first chart of a pair. -/
abbrev leftBase (p : PairIndex f g) :
    BoundedAlgHom K (C.atlas.algebra (base f g p)) (A.atlas.algebra p.1.1) :=
  f.pullback p.1.1 (base f g p) (isCommonBase_base f g p).1

/-- The pullback from the chosen base chart to the second chart of a pair. -/
abbrev rightBase (p : PairIndex f g) :
    BoundedAlgHom K (C.atlas.algebra (base f g p)) (B.atlas.algebra p.1.2) :=
  g.pullback p.1.2 (base f g p) (isCommonBase_base f g p).2

/-- The algebra of the chart `V_i ×_{W_k} U_j`: the affinoid pushout over the base chart. -/
abbrev algebra (p : PairIndex f g) : PresentedAffinoidAlgebra K :=
  AffinoidPushout.algebra (leftBase f g p) (rightBase f g p)

/-- The first leg `O(V_i) → O(V_i ×_{W_k} U_j)`. -/
abbrev leftMap (p : PairIndex f g) : BoundedAlgHom K (A.atlas.algebra p.1.1) (algebra f g p) :=
  AffinoidPushout.leftMap (leftBase f g p) (rightBase f g p)

/-- The second leg `O(U_j) → O(V_i ×_{W_k} U_j)`. -/
abbrev rightMap (p : PairIndex f g) : BoundedAlgHom K (B.atlas.algebra p.1.2) (algebra f g p) :=
  AffinoidPushout.rightMap (leftBase f g p) (rightBase f g p)

/-- The pushout square over every common base chart of the pair. -/
theorem condition (p : PairIndex f g) {k : C.atlas.Index} (hk : IsCommonBase f g p.1.1 p.1.2 k) :
    (leftMap f g p).comp (f.pullback p.1.1 k hk.1) = (rightMap f g p).comp (g.pullback p.1.2 k hk.2) :=
  condition_of_isCommonBase (isCommonBase_base f g p) hk _ _
    (AffinoidPushout.condition (leftBase f g p) (rightBase f g p))

/-! ## Inclusions of pairs -/

/-- Componentwise inclusion of chart ranges. -/
def Sub (p q : PairIndex f g) : Prop :=
  range (A.atlas.chart p.1.1) ⊆ range (A.atlas.chart q.1.1) ∧
    range (B.atlas.chart p.1.2) ⊆ range (B.atlas.chart q.1.2)

variable {f g} in
theorem IsCommonBase.mono {p q : PairIndex f g} (h : Sub f g p q) {k : C.atlas.Index}
    (hk : IsCommonBase f g q.1.1 q.1.2 k) : IsCommonBase f g p.1.1 p.1.2 k :=
  ⟨(image_mono h.1).trans hk.1, (image_mono h.2).trans hk.2⟩

theorem restriction_compat (p q : PairIndex f g) (h : Sub f g p q) :
    ((leftMap f g p).comp (A.atlas.restriction p.1.1 q.1.1 h.1)).comp (leftBase f g q) =
      ((rightMap f g p).comp (B.atlas.restriction p.1.2 q.1.2 h.2)).comp (rightBase f g q) := by
  have hq := (isCommonBase_base f g q).mono h
  have hl : (A.atlas.restriction p.1.1 q.1.1 h.1).comp (leftBase f g q) =
      f.pullback p.1.1 (base f g q) hq.1 := by
    have e := f.restriction_comm p.1.1 q.1.1 (base f g q) (base f g q) h.1 subset_rfl hq.1
      (isCommonBase_base f g q).1
    rw [C.atlas.restriction_id, BoundedAlgHom.comp_id] at e
    exact e
  have hr : (B.atlas.restriction p.1.2 q.1.2 h.2).comp (rightBase f g q) =
      g.pullback p.1.2 (base f g q) hq.2 := by
    have e := g.restriction_comm p.1.2 q.1.2 (base f g q) (base f g q) h.2 subset_rfl hq.2
      (isCommonBase_base f g q).2
    rw [C.atlas.restriction_id, BoundedAlgHom.comp_id] at e
    exact e
  rw [BoundedAlgHom.comp_assoc, hl, BoundedAlgHom.comp_assoc, hr]
  exact condition f g p hq

/-- The restriction `O(V_{i'} ×_W U_{j'}) → O(V_i ×_W U_j)` for an inclusion of pairs. -/
def restriction (p q : PairIndex f g) (h : Sub f g p q) :
    BoundedAlgHom K (algebra f g q) (algebra f g p) :=
  AffinoidPushout.lift (leftBase f g q) (rightBase f g q) (algebra f g p)
    ((leftMap f g p).comp (A.atlas.restriction p.1.1 q.1.1 h.1))
    ((rightMap f g p).comp (B.atlas.restriction p.1.2 q.1.2 h.2))
    (restriction_compat f g p q h)

theorem restriction_comp_leftMap (p q : PairIndex f g) (h : Sub f g p q) :
    (restriction f g p q h).comp (leftMap f g q) =
      (leftMap f g p).comp (A.atlas.restriction p.1.1 q.1.1 h.1) :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem restriction_comp_rightMap (p q : PairIndex f g) (h : Sub f g p q) :
    (restriction f g p q h).comp (rightMap f g q) =
      (rightMap f g p).comp (B.atlas.restriction p.1.2 q.1.2 h.2) :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

theorem sub_refl (p : PairIndex f g) : Sub f g p p := ⟨subset_rfl, subset_rfl⟩

theorem sub_trans {p q r : PairIndex f g} (h₁ : Sub f g p q) (h₂ : Sub f g q r) :
    Sub f g p r :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem restriction_refl (p : PairIndex f g) :
    restriction f g p p (sub_refl f g p) = BoundedAlgHom.id K (algebra f g p) := by
  apply AffinoidPushout.hom_ext
  · rw [restriction_comp_leftMap, A.atlas.restriction_id, BoundedAlgHom.comp_id,
      BoundedAlgHom.id_comp]
  · rw [restriction_comp_rightMap, B.atlas.restriction_id, BoundedAlgHom.comp_id,
      BoundedAlgHom.id_comp]

theorem restriction_trans {p q r : PairIndex f g} (h₁ : Sub f g p q) (h₂ : Sub f g q r) :
    restriction f g p r (sub_trans f g h₁ h₂) =
      (restriction f g p q h₁).comp (restriction f g q r h₂) := by
  apply AffinoidPushout.hom_ext
  · rw [restriction_comp_leftMap, BoundedAlgHom.comp_assoc, restriction_comp_leftMap,
      ← BoundedAlgHom.comp_assoc, restriction_comp_leftMap, BoundedAlgHom.comp_assoc,
      ← A.atlas.restriction_comp]
  · rw [restriction_comp_rightMap, BoundedAlgHom.comp_assoc, restriction_comp_rightMap,
      ← BoundedAlgHom.comp_assoc, restriction_comp_rightMap, BoundedAlgHom.comp_assoc,
      ← B.atlas.restriction_comp]

/-! ## Points and the image of a restriction -/

/-- The first projection of a point of a pair chart. -/
abbrev leftPoint (p : PairIndex f g) (s : BanachSpectrum (algebra f g p)) :
    BanachSpectrum (A.atlas.algebra p.1.1) :=
  BanachSpectrum.comap (leftMap f g p).toBoundedRingHom s

/-- The second projection of a point of a pair chart. -/
abbrev rightPoint (p : PairIndex f g) (s : BanachSpectrum (algebra f g p)) :
    BanachSpectrum (B.atlas.algebra p.1.2) :=
  BanachSpectrum.comap (rightMap f g p).toBoundedRingHom s

theorem leftPoint_pull (p q : PairIndex f g) (h : Sub f g p q) (s : BanachSpectrum (algebra f g p)) :
    leftPoint f g q (BanachSpectrum.comap (restriction f g p q h).toBoundedRingHom s) =
      BanachSpectrum.comap (A.atlas.restriction p.1.1 q.1.1 h.1).toBoundedRingHom
        (leftPoint f g p s) := by
  change BanachSpectrum.comap ((restriction f g p q h).comp (leftMap f g q)).toBoundedRingHom s = _
  rw [restriction_comp_leftMap]
  rfl

theorem rightPoint_pull (p q : PairIndex f g) (h : Sub f g p q) (s : BanachSpectrum (algebra f g p)) :
    rightPoint f g q (BanachSpectrum.comap (restriction f g p q h).toBoundedRingHom s) =
      BanachSpectrum.comap (B.atlas.restriction p.1.2 q.1.2 h.2).toBoundedRingHom
        (rightPoint f g p s) := by
  change BanachSpectrum.comap ((restriction f g p q h).comp (rightMap f g q)).toBoundedRingHom s = _
  rw [restriction_comp_rightMap]
  rfl

theorem chart_leftPoint_pull (p q : PairIndex f g) (h : Sub f g p q)
    (s : BanachSpectrum (algebra f g p)) :
    A.atlas.chart q.1.1 (leftPoint f g q (BanachSpectrum.comap (restriction f g p q h).toBoundedRingHom s)) =
      A.atlas.chart p.1.1 (leftPoint f g p s) := by
  rw [leftPoint_pull]
  exact A.atlas.restriction_chart p.1.1 q.1.1 h.1 _

theorem chart_rightPoint_pull (p q : PairIndex f g) (h : Sub f g p q)
    (s : BanachSpectrum (algebra f g p)) :
    B.atlas.chart q.1.2 (rightPoint f g q (BanachSpectrum.comap (restriction f g p q h).toBoundedRingHom s)) =
      B.atlas.chart p.1.2 (rightPoint f g p s) := by
  rw [rightPoint_pull]
  exact B.atlas.restriction_chart p.1.2 q.1.2 h.2 _

/-- The domain of `O(V_{i'} ×_W U_{j'})` of points whose projections lie in `V_i` and `U_j`. -/
def subDomain (p q : PairIndex f g) (h : Sub f g p q) : Domain K (algebra f g q) :=
  (Domain.pullback (leftMap f g q) (A.atlas.restrictionDomain p.1.1 q.1.1 h.1)).inter
    (Domain.pullback (rightMap f g q) (B.atlas.restrictionDomain p.1.2 q.1.2 h.2))

theorem mem_subDomain_locus (p q : PairIndex f g) (h : Sub f g p q)
    (t : BanachSpectrum (algebra f g q)) :
    t ∈ (subDomain f g p q h).locus ↔
      A.atlas.chart q.1.1 (leftPoint f g q t) ∈ range (A.atlas.chart p.1.1) ∧
        B.atlas.chart q.1.2 (rightPoint f g q t) ∈ range (B.atlas.chart p.1.2) :=
  Iff.rfl

theorem hasImageIn_restriction (p q : PairIndex f g) (h : Sub f g p q) :
    HasImageIn K (restriction f g p q h) (subDomain f g p q h).locus := by
  intro s
  rw [mem_subDomain_locus, chart_leftPoint_pull, chart_rightPoint_pull]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem restriction_universal (p q : PairIndex f g) (h : Sub f g p q)
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (algebra f g q) R)
    (hφ : HasImageIn K φ (subDomain f g p q h).locus) :
    ∃! ψ : BoundedAlgHom K (algebra f g p) R, ψ.comp (restriction f g p q h) = φ := by
  have hl : ∀ x : BanachSpectrum R, A.atlas.chart q.1.1
      (BanachSpectrum.comap (φ.comp (leftMap f g q)).toBoundedRingHom x) ∈
        range (A.atlas.chart p.1.1) := fun x => ((mem_subDomain_locus f g p q h _).1 (hφ x)).1
  have hr : ∀ x : BanachSpectrum R, B.atlas.chart q.1.2
      (BanachSpectrum.comap (φ.comp (rightMap f g q)).toBoundedRingHom x) ∈
        range (B.atlas.chart p.1.2) := fun x => ((mem_subDomain_locus f g p q h _).1 (hφ x)).2
  obtain ⟨α, hα, hαu⟩ := A.atlas.restriction_universal p.1.1 q.1.1 h.1 R _ hl
  obtain ⟨β, hβ, hβu⟩ := B.atlas.restriction_universal p.1.2 q.1.2 h.2 R _ hr
  have hq := (isCommonBase_base f g q).mono h
  have hcompat : α.comp (leftBase f g p) = β.comp (rightBase f g p) := by
    refine condition_of_isCommonBase hq (isCommonBase_base f g p) α β ?_
    have el := f.restriction_comm p.1.1 q.1.1 (base f g q) (base f g q) h.1 subset_rfl hq.1
      (isCommonBase_base f g q).1
    have er := g.restriction_comm p.1.2 q.1.2 (base f g q) (base f g q) h.2 subset_rfl hq.2
      (isCommonBase_base f g q).2
    rw [C.atlas.restriction_id, BoundedAlgHom.comp_id] at el er
    rw [← el, ← er, ← BoundedAlgHom.comp_assoc, hα, ← BoundedAlgHom.comp_assoc, hβ,
      BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc]
    exact congrArg φ.comp (AffinoidPushout.condition (leftBase f g q) (rightBase f g q))
  refine ⟨AffinoidPushout.lift (leftBase f g p) (rightBase f g p) R α β hcompat, ?_, ?_⟩
  · apply AffinoidPushout.hom_ext
    · rw [BoundedAlgHom.comp_assoc, restriction_comp_leftMap, ← BoundedAlgHom.comp_assoc,
        AffinoidPushout.lift_comp_leftMap, hα]
    · rw [BoundedAlgHom.comp_assoc, restriction_comp_rightMap, ← BoundedAlgHom.comp_assoc,
        AffinoidPushout.lift_comp_rightMap, hβ]
  · intro ψ hψ
    apply AffinoidPushout.hom_ext
    · rw [AffinoidPushout.lift_comp_leftMap]
      apply hαu
      rw [BoundedAlgHom.comp_assoc, ← restriction_comp_leftMap f g p q h, ← BoundedAlgHom.comp_assoc, hψ]
    · rw [AffinoidPushout.lift_comp_rightMap]
      apply hβu
      rw [BoundedAlgHom.comp_assoc, ← restriction_comp_rightMap f g p q h, ← BoundedAlgHom.comp_assoc, hψ]

theorem represents_restriction (p q : PairIndex f g) (h : Sub f g p q) :
    Represents K (restriction f g p q h) (subDomain f g p q h).locus :=
  represents_of_universal _ _ (hasImageIn_restriction f g p q h)
    (restriction_universal f g p q h)

theorem range_restriction (p q : PairIndex f g) (h : Sub f g p q) :
    range (BanachSpectrum.comap (restriction f g p q h).toBoundedRingHom) =
      (subDomain f g p q h).locus :=
  (represents_restriction f g p q h).2.1

theorem mem_range_restriction_iff (p q : PairIndex f g) (h : Sub f g p q)
    (t : BanachSpectrum (algebra f g q)) :
    t ∈ range (BanachSpectrum.comap (restriction f g p q h).toBoundedRingHom) ↔
      A.atlas.chart q.1.1 (leftPoint f g q t) ∈ range (A.atlas.chart p.1.1) ∧
        B.atlas.chart q.1.2 (rightPoint f g q t) ∈ range (B.atlas.chart p.1.2) := by
  rw [range_restriction]
  rfl

/-! ## The chart system -/

/-- The chart system of the fibre product: pairs of charts with a common base chart,
with the affinoid pushouts over the base as chart algebras. -/
abbrev chartSystem : AffinoidChartSystem.{u, w} K where
  Index := PairIndex f g
  algebra := algebra f g
  Sub := Sub f g
  restriction := restriction f g
  sub_refl := sub_refl f g
  sub_trans := sub_trans f g
  restriction_refl := restriction_refl f g
  restriction_trans := restriction_trans f g
  represents p q h := by
    rw [range_restriction]
    exact represents_restriction f g p q h
  meet := by
    intro p q r hpr hqr t htp htq
    rw [mem_range_restriction_iff] at htp htq
    obtain ⟨m₁, hm₁, hx₁⟩ := IndexedAffinoidAtlas.exists_chart_inter htp.1 htq.1
    obtain ⟨m₂, hm₂, hx₂⟩ := IndexedAffinoidAtlas.exists_chart_inter htp.2 htq.2
    let l : PairIndex f g := ⟨(m₁, m₂), base f g p,
      ⟨(image_mono (hm₁.trans inter_subset_left)).trans (isCommonBase_base f g p).1,
        (image_mono (hm₂.trans inter_subset_left)).trans (isCommonBase_base f g p).2⟩⟩
    refine ⟨l, ⟨hm₁.trans inter_subset_left, hm₂.trans inter_subset_left⟩,
      ⟨hm₁.trans inter_subset_right, hm₂.trans inter_subset_right⟩, ?_⟩
    rw [mem_range_restriction_iff]
    exact ⟨hx₁, hx₂⟩

/-! ## Projections -/

/-- The first projection from the glued fibre product to `X`. -/
def fst : (chartSystem f g).Space → A.space :=
  Quotient.lift (fun z => A.atlas.chart z.1.1.1 (leftPoint f g z.1 z.2)) (by
    rintro ⟨p, s⟩ ⟨q, t⟩ ⟨k, hkp, hkq, v, hvs, hvt⟩
    change A.atlas.chart p.1.1 (leftPoint f g p s) = A.atlas.chart q.1.1 (leftPoint f g q t)
    have hvs' : (chartSystem f g).pull hkp v = s := hvs
    have hvt' : (chartSystem f g).pull hkq v = t := hvt
    rw [← hvs', ← hvt']
    exact (chart_leftPoint_pull f g k p hkp v).trans (chart_leftPoint_pull f g k q hkq v).symm)

/-- The second projection from the glued fibre product to `Y`. -/
def snd : (chartSystem f g).Space → B.space :=
  Quotient.lift (fun z => B.atlas.chart z.1.1.2 (rightPoint f g z.1 z.2)) (by
    rintro ⟨p, s⟩ ⟨q, t⟩ ⟨k, hkp, hkq, v, hvs, hvt⟩
    change B.atlas.chart p.1.2 (rightPoint f g p s) = B.atlas.chart q.1.2 (rightPoint f g q t)
    have hvs' : (chartSystem f g).pull hkp v = s := hvs
    have hvt' : (chartSystem f g).pull hkq v = t := hvt
    rw [← hvs', ← hvt']
    exact (chart_rightPoint_pull f g k p hkp v).trans (chart_rightPoint_pull f g k q hkq v).symm)

theorem fst_chart (p : PairIndex f g) (s : BanachSpectrum (algebra f g p)) :
    fst f g ((chartSystem f g).chart p s) = A.atlas.chart p.1.1 (leftPoint f g p s) := rfl

theorem snd_chart (p : PairIndex f g) (s : BanachSpectrum (algebra f g p)) :
    snd f g ((chartSystem f g).chart p s) = B.atlas.chart p.1.2 (rightPoint f g p s) := rfl

theorem continuous_fst : Continuous (fst f g) := by
  apply Continuous.quotient_lift
  refine continuous_sigma fun p => ?_
  show Continuous (fun s : BanachSpectrum (algebra f g p) => A.atlas.chart p.1.1 (leftPoint f g p s))
  exact (A.atlas.isEmbedding_chart p.1.1).continuous.comp
    (BanachSpectrum.comapContinuous _).continuous

theorem continuous_snd : Continuous (snd f g) := by
  apply Continuous.quotient_lift
  refine continuous_sigma fun p => ?_
  show Continuous (fun s : BanachSpectrum (algebra f g p) => B.atlas.chart p.1.2 (rightPoint f g p s))
  exact (B.atlas.isEmbedding_chart p.1.2).continuous.comp
    (BanachSpectrum.comapContinuous _).continuous

/-- The square `f ∘ fst = g ∘ snd`. -/
theorem baseMap_fst (z : (chartSystem f g).Space) : f.baseMap (fst f g z) = g.baseMap (snd f g z) := by
  obtain ⟨p, s, rfl⟩ := (chartSystem f g).exists_chart z
  rw [fst_chart, snd_chart, ← f.chart_comm p.1.1 (base f g p) (isCommonBase_base f g p).1,
    ← g.chart_comm p.1.2 (base f g p) (isCommonBase_base f g p).2]
  change C.atlas.chart (base f g p) (BanachSpectrum.comap
      ((leftMap f g p).comp (leftBase f g p)).toBoundedRingHom s) =
    C.atlas.chart (base f g p) (BanachSpectrum.comap
      ((rightMap f g p).comp (rightBase f g p)).toBoundedRingHom s)
  rw [AffinoidPushout.condition]

/-- A point of the glued fibre product lies in the chart of a pair exactly when its two
projections lie in the two chart ranges. -/
theorem mem_range_chart_iff (p : PairIndex f g) (z : (chartSystem f g).Space) :
    z ∈ range ((chartSystem f g).chart p) ↔
      fst f g z ∈ range (A.atlas.chart p.1.1) ∧ snd f g z ∈ range (B.atlas.chart p.1.2) := by
  let Q := chartSystem f g
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨q, t, rfl⟩ := Q.exists_chart z
    rw [fst_chart] at hx
    rw [snd_chart] at hy
    obtain ⟨m₁, hm₁, hx₁⟩ := IndexedAffinoidAtlas.exists_chart_inter hx ⟨_, rfl⟩
    obtain ⟨m₂, hm₂, hx₂⟩ := IndexedAffinoidAtlas.exists_chart_inter hy ⟨_, rfl⟩
    let m : PairIndex f g := ⟨(m₁, m₂), base f g q,
      ⟨(image_mono (hm₁.trans inter_subset_right)).trans (isCommonBase_base f g q).1,
        (image_mono (hm₂.trans inter_subset_right)).trans (isCommonBase_base f g q).2⟩⟩
    have hmq : Sub f g m q := ⟨hm₁.trans inter_subset_right, hm₂.trans inter_subset_right⟩
    have hmp : Sub f g m p := ⟨hm₁.trans inter_subset_left, hm₂.trans inter_subset_left⟩
    obtain ⟨v, hv⟩ := (mem_range_restriction_iff f g m q hmq t).2 ⟨hx₁, hx₂⟩
    refine ⟨Q.pull hmp v, ?_⟩
    have hv' : Q.pull hmq v = t := hv
    rw [Q.chart_pull hmp v, ← hv', Q.chart_pull hmq v]

theorem range_chart (p : PairIndex f g) :
    range ((chartSystem f g).chart p) =
      fst f g ⁻¹' range (A.atlas.chart p.1.1) ∩ snd f g ⁻¹' range (B.atlas.chart p.1.2) := by
  ext z
  exact mem_range_chart_iff f g p z

/-! ## Finite overlaps -/

/-- If both spaces are Hausdorff, the fibre product chart system has finite overlaps. -/
theorem hasFiniteOverlaps [T2Space A.space] [T2Space B.space] :
    (chartSystem f g).HasFiniteOverlaps := by
  intro p q
  obtain ⟨S₁, hS₁, hS₁sub, hS₁cov⟩ :=
    IndexedAffinoidAtlas.exists_finite_charts_inter (a := A.atlas) p.1.1 q.1.1
  obtain ⟨S₂, hS₂, hS₂sub, hS₂cov⟩ :=
    IndexedAffinoidAtlas.exists_finite_charts_inter (a := B.atlas) p.1.2 q.1.2
  let Q := chartSystem f g
  have hinj : Function.Injective
      (fun k : {k : PairIndex f g // Q.Sub k p ∧ Q.Sub k q} => k.1.1) :=
    Subtype.val_injective.comp Subtype.val_injective
  refine ⟨{k | k.1.1.1 ∈ S₁ ∧ k.1.1.2 ∈ S₂},
    ((hS₁.prod hS₂).preimage hinj.injOn).subset fun k hk => hk, ?_⟩
  intro s t hst
  have hglued := hst
  obtain ⟨k, hkp, hkq, v, hvs, hvt⟩ := hst
  have hcpq : Q.chart p s = Q.chart q t := Q.chart_eq_iff.2 hglued
  have hx₁ : A.atlas.chart p.1.1 (leftPoint f g p s) ∈
      range (A.atlas.chart p.1.1) ∩ range (A.atlas.chart q.1.1) :=
    ⟨⟨_, rfl⟩, ⟨_, (congrArg (fst f g) hcpq).symm⟩⟩
  have hx₂ : B.atlas.chart p.1.2 (rightPoint f g p s) ∈
      range (B.atlas.chart p.1.2) ∩ range (B.atlas.chart q.1.2) :=
    ⟨⟨_, rfl⟩, ⟨_, (congrArg (snd f g) hcpq).symm⟩⟩
  obtain ⟨m₁, hm₁S, hm₁⟩ := mem_iUnion₂.1 (hS₁cov hx₁)
  obtain ⟨m₂, hm₂S, hm₂⟩ := mem_iUnion₂.1 (hS₂cov hx₂)
  let m : PairIndex f g := ⟨(m₁, m₂), base f g p,
    ⟨(image_mono ((hS₁sub m₁ hm₁S).trans inter_subset_left)).trans
        (isCommonBase_base f g p).1,
      (image_mono ((hS₂sub m₂ hm₂S).trans inter_subset_left)).trans
        (isCommonBase_base f g p).2⟩⟩
  have hsubp : Sub f g m p :=
    ⟨(hS₁sub m₁ hm₁S).trans inter_subset_left, (hS₂sub m₂ hm₂S).trans inter_subset_left⟩
  have hsubq : Sub f g m q :=
    ⟨(hS₁sub m₁ hm₁S).trans inter_subset_right, (hS₂sub m₂ hm₂S).trans inter_subset_right⟩
  have hsr : s ∈ range (BanachSpectrum.comap (restriction f g m p hsubp).toBoundedRingHom) :=
    (mem_range_restriction_iff f g m p hsubp s).2 ⟨hm₁, hm₂⟩
  obtain ⟨v', hv'⟩ := hsr
  refine ⟨⟨m, hsubp, hsubq⟩, ⟨hm₁S, hm₂S⟩, v', hv', ?_⟩
  apply Q.chart_injective q
  have h1 : Q.chart q (Q.pull hsubq v') = Q.chart m v' := Q.chart_pull hsubq v'
  have h2 : Q.chart p (Q.pull hsubp v') = Q.chart m v' := Q.chart_pull hsubp v'
  have h3 : Q.pull hsubp v' = s := hv'
  rw [h3] at h2
  exact h1.trans (h2.symm.trans hcpq)

/-- If both spaces are Hausdorff, the fibre product charts are closed embeddings. -/
theorem isClosedEmbedding_chart [T2Space A.space] [T2Space B.space] (p : PairIndex f g) :
    IsClosedEmbedding ((chartSystem f g).chart p) :=
  (chartSystem f g).isClosedEmbedding_chart (hasFiniteOverlaps f g) p

end FibreProduct

end Langlands.Analytic
