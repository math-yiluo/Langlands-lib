import Langlands.Geometry.Analytic.AtlasDomainRestrictionGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange

/-! # Full representation of local domains in arbitrary containing original charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- The literal ambient image expressed in the second chart's coordinates. -/
def domainChartLocus (i j : a.Index) (U : Domain K (a.algebra i)) :
    Set (BanachSpectrum (a.algebra j)) :=
  a.chart j ⁻¹' (a.chart i '' U.locus)

namespace CompactIntersectionChartCover

variable {a} {i j : a.Index} {U : Domain K (a.algebra i)}
  (c : a.CompactIntersectionChartCover i j (a.chart i '' U.locus))

/-- The constructed bounded map has precisely the required spectrum image. -/
theorem range_glueChartRestriction :
    Set.range (BanachSpectrum.comap c.glueChartRestriction.toBoundedRingHom) =
      a.domainChartLocus i j U := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨U.spectrumMap y, U.represents.hasImageIn y,
      (c.glueChartRestriction_chart y).symm⟩
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨y, hy⟩ := U.represents.2.1.symm ▸ hz
    refine ⟨y, (a.isEmbedding_chart j).injective ?_⟩
    exact (c.glueChartRestriction_chart y).trans ((congrArg (a.chart i) hy).trans hzx)

/-- The transported covering domains cover the literal locus in the second chart. -/
theorem rightChartDomains_cover (x : BanachSpectrum (a.algebra j))
    (hx : x ∈ a.domainChartLocus i j U) :
    ∃ t, x ∈ (c.domainOverRightChart t).locus := by
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨t, ht⟩ := c.domainCover.covers z hz
  have hx' : a.chart j x ∈ a.chart i '' (c.domainCover.obj t).locus := ⟨z, ht, hzx⟩
  rw [← c.chart_image_domainOverRightChart t] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  exact ⟨t, (a.isEmbedding_chart j).injective hyx ▸ hy⟩

/-- On any full-domain overlap in the second chart, the original first-chart
structural maps agree as complete bounded algebra maps. -/
theorem overlap_firstBaseMap (t s : Fin c.size)
    (W : Domain K (a.algebra j))
    (f : W ⟶ c.domainOverRightChart t) (g : W ⟶ c.domainOverRightChart s) :
    f.restriction.comp (c.domainCover.obj t).baseMap =
      g.restriction.comp (c.domainCover.obj s).baseMap := by
  have heq := a.originalChartRestriction_overlap j i (c.index t) (c.index s)
    (c.right_subset t) (c.left_subset t) (c.right_subset s) (c.left_subset s) W
    (f ≫ a.extendDomainInclusion (c.index t) j (c.right_subset t) (c.domainOverChart t))
    (g ≫ a.extendDomainInclusion (c.index s) j (c.right_subset s) (c.domainOverChart s))
  change (f.restriction.comp (c.domainCoverToChart t).restriction).comp
      (a.restriction (c.index t) i (c.left_subset t)) =
    (g.restriction.comp (c.domainCoverToChart s).restriction).comp
      (a.restriction (c.index s) i (c.left_subset s)) at heq
  erw [BoundedAlgHom.comp_assoc, (c.domainCoverToChart t).comp_baseMap,
    BoundedAlgHom.comp_assoc, (c.domainCoverToChart s).comp_baseMap] at heq
  exact heq

/-- Factoring an arbitrary affinoid test through the full intersection
transports second-chart agreement to first-chart agreement. -/
theorem firstBaseMap_eq_of_secondBaseMap_eq (t s : Fin c.size)
    (R : PresentedAffinoidAlgebra K)
    (α : BoundedAlgHom K (c.domainCover.obj t).algebra R)
    (β : BoundedAlgHom K (c.domainCover.obj s).algebra R)
    (h : α.comp (c.chartRestrictionFamily t) = β.comp (c.chartRestrictionFamily s)) :
    α.comp (c.domainCover.obj t).baseMap =
      β.comp (c.domainCover.obj s).baseMap := by
  let D := c.domainOverRightChart t
  let E := c.domainOverRightChart s
  let W := D.inter E
  have himage : HasImageIn K (α.comp D.baseMap) W.locus := by
    intro x
    refine ⟨D.represents.hasImageIn (BanachSpectrum.comap α.toBoundedRingHom x), ?_⟩
    have hx := E.represents.hasImageIn (BanachSpectrum.comap β.toBoundedRingHom x)
    have heq : BanachSpectrum.comap (α.comp D.baseMap).toBoundedRingHom x =
        BanachSpectrum.comap (β.comp E.baseMap).toBoundedRingHom x :=
      congrArg (fun q : BoundedAlgHom K (a.algebra j) R =>
        BanachSpectrum.comap q.toBoundedRingHom x) h
    exact heq.symm ▸ hx
  obtain ⟨θ, hθ, _⟩ := W.represents.2.2 R (α.comp D.baseMap) himage
  have hα : θ.comp (Domain.interLeft D E).restriction = α := by
    apply D.represents.hom_ext R
    erw [BoundedAlgHom.comp_assoc, (Domain.interLeft D E).comp_baseMap, hθ]
    rfl
  have hβ : θ.comp (Domain.interRight D E).restriction = β := by
    apply E.represents.hom_ext R
    erw [BoundedAlgHom.comp_assoc, (Domain.interRight D E).comp_baseMap, hθ]
    exact h
  have heq := c.overlap_firstBaseMap t s W (Domain.interLeft D E) (Domain.interRight D E)
  have hθeq := congrArg (fun q : BoundedAlgHom K (a.algebra i) W.algebra => θ.comp q) heq
  calc
    α.comp (c.domainCover.obj t).baseMap =
        (θ.comp (Domain.interLeft D E).restriction).comp (c.domainCover.obj t).baseMap :=
      congrArg (fun q : BoundedAlgHom K (c.domainCover.obj t).algebra R =>
        q.comp (c.domainCover.obj t).baseMap) hα.symm
    _ = (θ.comp (Domain.interRight D E).restriction).comp
        (c.domainCover.obj s).baseMap := hθeq
    _ = β.comp (c.domainCover.obj s).baseMap :=
      congrArg (fun q : BoundedAlgHom K (c.domainCover.obj s).algebra R =>
        q.comp (c.domainCover.obj s).baseMap) hβ

/-- The same agreement determines complete maps from the unchanged U algebra. -/
theorem restriction_eq_of_secondBaseMap_eq (t s : Fin c.size)
    (R : PresentedAffinoidAlgebra K)
    (α : BoundedAlgHom K (c.domainCover.obj t).algebra R)
    (β : BoundedAlgHom K (c.domainCover.obj s).algebra R)
    (h : α.comp (c.chartRestrictionFamily t) = β.comp (c.chartRestrictionFamily s)) :
    α.comp (c.domainCover.map t).restriction =
      β.comp (c.domainCover.map s).restriction := by
  apply U.represents.hom_ext R
  erw [BoundedAlgHom.comp_assoc, (c.domainCover.map t).comp_baseMap,
    BoundedAlgHom.comp_assoc, (c.domainCover.map s).comp_baseMap]
  exact c.firstBaseMap_eq_of_secondBaseMap_eq t s R α β h

/-- Pulling back every transported member covers the whole test spectrum. -/
def testCover (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R)
    (hφ : HasImageIn K φ (a.domainChartLocus i j U)) :
    Domain.FiniteCover (Domain.whole K R) where
  size := c.size
  obj t := Domain.pullback φ (c.domainOverRightChart t)
  map t := ⟨(Domain.pullback φ (c.domainOverRightChart t)).baseMap,
    BoundedAlgHom.comp_id _⟩
  covers x _ := c.rightChartDomains_cover (BanachSpectrum.comap φ.toBoundedRingHom x) (hφ x)

/-- The actual second pushout leg, composed with the original U restriction. -/
def testLocalMap (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R)
    (hφ : HasImageIn K φ (a.domainChartLocus i j U)) (t : Fin c.size) :
    BoundedAlgHom K U.algebra ((c.testCover R φ hφ).obj t).algebra :=
  (Domain.pullbackMap φ (c.domainOverRightChart t)).comp (c.domainCover.map t).restriction

/-- The pulled maps agree on every full-domain test; no new universal
property for the glued output is used in this compatibility proof. -/
theorem testLocalMap_compatible (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R)
    (hφ : HasImageIn K φ (a.domainChartLocus i j U)) :
    (c.testCover R φ hφ).BoundedMapCompatible (c.testLocalMap R φ hφ) := by
  intro t s W p q
  let α := p.restriction.comp (Domain.pullbackMap φ (c.domainOverRightChart t))
  let β := q.restriction.comp (Domain.pullbackMap φ (c.domainOverRightChart s))
  have hα : α.comp (c.chartRestrictionFamily t) = W.baseMap.comp φ := by
    change (p.restriction.comp (Domain.pullbackMap φ (c.domainOverRightChart t))).comp
        (c.domainOverRightChart t).baseMap = W.baseMap.comp φ
    erw [BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, p.comp_baseMap]
  have hβ : β.comp (c.chartRestrictionFamily s) = W.baseMap.comp φ := by
    change (q.restriction.comp (Domain.pullbackMap φ (c.domainOverRightChart s))).comp
        (c.domainOverRightChart s).baseMap = W.baseMap.comp φ
    erw [BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, q.comp_baseMap]
  exact c.restriction_eq_of_secondBaseMap_eq t s W.algebra α β (hα.trans hβ.symm)

/-- Bounded descent constructs a global factor on each eligible affinoid test. -/
def testFactor (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R)
    (hφ : HasImageIn K φ (a.domainChartLocus i j U)) :
    BoundedAlgHom K U.algebra R :=
  (c.testCover R φ hφ).glueBoundedAlgHom (c.testLocalMap R φ hφ)
    (c.testLocalMap_compatible R φ hφ)

theorem testFactor_local (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R)
    (hφ : HasImageIn K φ (a.domainChartLocus i j U)) (t : Fin c.size) :
    (Domain.pullback φ (c.domainOverRightChart t)).baseMap.comp (c.testFactor R φ hφ) =
      c.testLocalMap R φ hφ t :=
  (c.testCover R φ hφ).restriction_comp_glueBoundedAlgHom _ _ t

theorem testFactor_comp (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R)
    (hφ : HasImageIn K φ (a.domainChartLocus i j U)) :
    (c.testFactor R φ hφ).comp c.glueChartRestriction = φ := by
  apply BoundedAlgHom.ext
  intro b
  apply (c.testCover R φ hφ).algebra_ext_of_restrict_eq
  intro t
  have heq :
      ((c.testCover R φ hφ).map t).restriction.comp
          ((c.testFactor R φ hφ).comp c.glueChartRestriction) =
        ((c.testCover R φ hφ).map t).restriction.comp φ := by
    have h₁ := congrArg (fun f : BoundedAlgHom K U.algebra
      ((c.testCover R φ hφ).obj t).algebra => f.comp c.glueChartRestriction)
      (c.testFactor_local R φ hφ t)
    have h₂ := congrArg (fun f : BoundedAlgHom K (a.algebra j)
      (c.domainCover.obj t).algebra =>
        (Domain.pullbackMap φ (c.domainOverRightChart t)).comp f)
      (c.restriction_comp_glueChartRestriction t)
    exact h₁.trans (h₂.trans (Domain.pullbackMap_comp_baseMap φ (c.domainOverRightChart t)))
  exact congrArg (fun f : BoundedAlgHom K (a.algebra j)
    ((c.testCover R φ hφ).obj t).algebra => f b) heq

/-- Any competing factor has the forced original ambient chart equation. -/
theorem factor_chart (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R) (θ : BoundedAlgHom K U.algebra R)
    (hθ : θ.comp c.glueChartRestriction = φ) (x : BanachSpectrum R) :
    a.chart i (U.spectrumMap (BanachSpectrum.comap θ.toBoundedRingHom x)) =
      a.chart j (BanachSpectrum.comap φ.toBoundedRingHom x) := by
  have heq :
      BanachSpectrum.comap c.glueChartRestriction.toBoundedRingHom
          (BanachSpectrum.comap θ.toBoundedRingHom x) =
        BanachSpectrum.comap φ.toBoundedRingHom x := by
    apply BanachSpectrum.ext
    intro b
    exact congrArg (fun q : BoundedAlgHom K (a.algebra j) R => x (q b)) hθ
  exact (c.glueChartRestriction_chart _).symm.trans (congrArg (a.chart j) heq)

/-- On the pulled member, every competing factor lands in the corresponding
original relative full domain over U.algebra. -/
theorem factor_imageIn_relative (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R) (θ : BoundedAlgHom K U.algebra R)
    (hθ : θ.comp c.glueChartRestriction = φ) (t : Fin c.size) :
    HasImageIn K ((Domain.pullback φ (c.domainOverRightChart t)).baseMap.comp θ)
      (U.relative (c.domainCover.obj t) (c.domainCover.map t)).locus := by
  rw [U.relative_locus_eq_preimage_of_injective U.spectrumMap_injective]
  intro x
  have hx := (Domain.pullback φ (c.domainOverRightChart t)).represents.hasImageIn x
  have hmem :
      a.chart j (BanachSpectrum.comap φ.toBoundedRingHom
          ((Domain.pullback φ (c.domainOverRightChart t)).spectrumMap x)) ∈
        a.chart i '' (c.domainCover.obj t).locus := by
    rw [← c.chart_image_domainOverRightChart t]
    exact ⟨_, hx, rfl⟩
  rw [← c.factor_chart R φ θ hθ] at hmem
  obtain ⟨z, hz, hzx⟩ := hmem
  change U.spectrumMap (BanachSpectrum.comap θ.toBoundedRingHom
    ((Domain.pullback φ (c.domainOverRightChart t)).spectrumMap x)) ∈
      (c.domainCover.obj t).locus
  exact (a.isEmbedding_chart i).injective hzx ▸ hz

/-- Full representation on the pulled member forces every competing factor
to have the same complete bounded local map. -/
theorem factor_local_eq (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R) (θ : BoundedAlgHom K U.algebra R)
    (hθ : θ.comp c.glueChartRestriction = φ) (t : Fin c.size) :
    (Domain.pullback φ (c.domainOverRightChart t)).baseMap.comp θ =
      (Domain.pullbackMap φ (c.domainOverRightChart t)).comp
        (c.domainCover.map t).restriction := by
  let Q := Domain.pullback φ (c.domainOverRightChart t)
  obtain ⟨γ, hγ, _⟩ :=
    (U.relative (c.domainCover.obj t) (c.domainCover.map t)).represents.2.2 Q.algebra
      (Q.baseMap.comp θ) (c.factor_imageIn_relative R φ θ hθ t)
  have hγj : γ.comp (c.chartRestrictionFamily t) = Q.baseMap.comp φ := by
    erw [← c.restriction_comp_glueChartRestriction t, ← BoundedAlgHom.comp_assoc]
    change (γ.comp (U.relative (c.domainCover.obj t) (c.domainCover.map t)).baseMap).comp
      c.glueChartRestriction = _
    erw [hγ, BoundedAlgHom.comp_assoc, hθ]
  have hγeq : γ = Domain.pullbackMap φ (c.domainOverRightChart t) :=
    (c.domainOverRightChart t).represents.hom_ext Q.algebra _ _
      (hγj.trans (Domain.pullbackMap_comp_baseMap φ (c.domainOverRightChart t)).symm)
  exact hγ.symm.trans
    (congrArg (fun q : BoundedAlgHom K (c.domainCover.obj t).algebra Q.algebra =>
      q.comp (c.domainCover.map t).restriction) hγeq)

/-- All eligible affinoid tests factor uniquely through the constructed map. -/
theorem testFactor_existsUnique (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra j) R)
    (hφ : HasImageIn K φ (a.domainChartLocus i j U)) :
    ∃! θ : BoundedAlgHom K U.algebra R, θ.comp c.glueChartRestriction = φ := by
  refine ⟨c.testFactor R φ hφ, c.testFactor_comp R φ hφ, ?_⟩
  intro θ hθ
  exact (c.testCover R φ hφ).glueBoundedAlgHom_unique
    (c.testLocalMap R φ hφ) (c.testLocalMap_compatible R φ hφ) θ
    (fun t => c.factor_local_eq R φ θ hθ t)

/-- The glued structural map represents the literal local-domain image
against every finite positive-polyradius affinoid test. -/
theorem represents_glueChartRestriction :
    Represents K c.glueChartRestriction (a.domainChartLocus i j U) := by
  refine ⟨?_, c.range_glueChartRestriction, c.testFactor_existsUnique⟩
  rw [← c.range_glueChartRestriction]
  exact (isCompact_range (BanachSpectrum.comapContinuous
    c.glueChartRestriction.toBoundedRingHom).continuous).isClosed

end CompactIntersectionChartCover

/-- Full representation of the constructed unrestricted original-chart map. -/
theorem domainChartRestriction_represents (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) :
    Represents K (a.domainChartRestriction i j U h) (a.domainChartLocus i j U) :=
  (a.domainImageChartCover i j U h).represents_glueChartRestriction

/-- The same actual local-domain algebra, now fully represented over any
original chart containing its ambient image. -/
def domainInChart (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) : Domain K (a.algebra j) where
  algebra := U.algebra
  baseMap := a.domainChartRestriction i j U h
  locus := a.domainChartLocus i j U
  represents := a.domainChartRestriction_represents i j U h

@[simp]
theorem domainInChart_algebra (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) :
    (a.domainInChart i j U h).algebra = U.algebra := rfl

@[simp]
theorem domainInChart_baseMap (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) :
    (a.domainInChart i j U h).baseMap = a.domainChartRestriction i j U h := rfl

@[simp]
theorem domainInChart_locus (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) :
    (a.domainInChart i j U h).locus = a.domainChartLocus i j U := rfl

theorem chart_image_domainInChart (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) :
    a.chart j '' (a.domainInChart i j U h).locus = a.chart i '' U.locus := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    obtain ⟨y, hy⟩ := h hx
    refine ⟨y, ?_, hy⟩
    change a.chart j y ∈ a.chart i '' U.locus
    exact hy.symm ▸ hx

end Langlands.Analytic.IndexedAffinoidAtlas
