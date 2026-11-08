import Langlands.Geometry.Analytic.AffinoidChartGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainProduct
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainIntersection
import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms
import Langlands.Geometry.Analytic.AtlasTopology.CompactSubcover
import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition

/-! # The chart system of the product of two analytic spaces -/

noncomputable section

universe u v v' w w'

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra.Domain

variable {A B : PresentedAffinoidAlgebra K}

/-- The structural map of the coproduct of two domain algebras represents the
product locus. -/
theorem represents_productBaseMap (U : Domain K A) (V : Domain K B) :
    Represents K (U.productBaseMap V) (U.product V).locus := by
  have h := Represents.postcomp_equiv (U.product V).represents (U.productCoproductEquiv V).symm
  have heq : (U.productCoproductEquiv V).symm.toBoundedAlgHom.comp (U.product V).baseMap =
      U.productBaseMap V :=
    (BoundedAlgHom.ext fun _ => rfl).trans (U.productToCoproductMap_comp_baseMap V)
  rwa [heq] at h

end PresentedAffinoidAlgebra.Domain

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] {Y : Type v'} [TopologicalSpace Y]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) (b : IndexedAffinoidAtlas.{u, v', w'} K Y)

/-- Componentwise containment of chart ranges. -/
abbrev ProductSub (p q : a.Index × b.Index) : Prop :=
  Set.range (a.chart p.1) ⊆ Set.range (a.chart q.1) ∧
    Set.range (b.chart p.2) ⊆ Set.range (b.chart q.2)

/-- The algebra of a product chart: the affinoid coproduct of the two chart
algebras. -/
abbrev productAlgebra (p : a.Index × b.Index) : PresentedAffinoidAlgebra K :=
  AffinoidCoproduct.algebra K (a.algebra p.1) (b.algebra p.2)

/-- The restriction between product charts: the coproduct of the two
restrictions. -/
def productRestriction (p q : a.Index × b.Index) (h : ProductSub a b p q) :
    BoundedAlgHom K (productAlgebra a b q) (productAlgebra a b p) :=
  (a.restrictionDomain p.1 q.1 h.1).productBaseMap (b.restrictionDomain p.2 q.2 h.2)

theorem productRestriction_comp_leftMap (p q : a.Index × b.Index) (h : ProductSub a b p q) :
    (productRestriction a b p q h).comp (AffinoidCoproduct.leftMap K (a.algebra q.1) (b.algebra q.2)) =
      (AffinoidCoproduct.leftMap K (a.algebra p.1) (b.algebra p.2)).comp
        (a.restriction p.1 q.1 h.1) :=
  Domain.productBaseMap_comp_leftMap _ _

theorem productRestriction_comp_rightMap (p q : a.Index × b.Index) (h : ProductSub a b p q) :
    (productRestriction a b p q h).comp (AffinoidCoproduct.rightMap K (a.algebra q.1) (b.algebra q.2)) =
      (AffinoidCoproduct.rightMap K (a.algebra p.1) (b.algebra p.2)).comp
        (b.restriction p.2 q.2 h.2) :=
  Domain.productBaseMap_comp_rightMap _ _

variable {a} in
/-- A point in two chart ranges lies in a chart range inside both, by the net
axiom of the atlas. -/
theorem exists_chart_inter {i j : a.Index} {x : X} (hi : x ∈ Set.range (a.chart i))
    (hj : x ∈ Set.range (a.chart j)) :
    ∃ m, Set.range (a.chart m) ⊆ Set.range (a.chart i) ∩ Set.range (a.chart j) ∧
      x ∈ Set.range (a.chart m) := by
  obtain ⟨σ, -, hστ, hxσ, hσN⟩ :=
    a.isNet_chartFamily.2 _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ (⟨x, hi, hj⟩ : ↥(Set.range (a.chart i) ∩
      Set.range (a.chart j)))
  obtain ⟨V, hVσ, -⟩ := Set.mem_sUnion.1 (mem_of_mem_nhds hσN)
  obtain ⟨W, ⟨m, rfl⟩, hWsub, rfl⟩ := hστ hVσ
  exact ⟨m, hWsub, hxσ _ hVσ⟩

theorem productRestriction_refl (p : a.Index × b.Index) :
    productRestriction a b p p ⟨subset_rfl, subset_rfl⟩ = BoundedAlgHom.id K _ := by
  apply AffinoidCoproduct.hom_ext K (productAlgebra a b p) (a.algebra p.1) (b.algebra p.2)
  · rw [productRestriction_comp_leftMap, a.restriction_id, BoundedAlgHom.comp_id,
      BoundedAlgHom.id_comp]
  · rw [productRestriction_comp_rightMap, b.restriction_id, BoundedAlgHom.comp_id,
      BoundedAlgHom.id_comp]

theorem productRestriction_trans {p q r : a.Index × b.Index} (hpq : ProductSub a b p q)
    (hqr : ProductSub a b q r) :
    productRestriction a b p r ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩ =
      (productRestriction a b p q hpq).comp (productRestriction a b q r hqr) := by
  apply AffinoidCoproduct.hom_ext K (productAlgebra a b p) (a.algebra r.1) (b.algebra r.2)
  · rw [productRestriction_comp_leftMap, BoundedAlgHom.comp_assoc,
      productRestriction_comp_leftMap, ← BoundedAlgHom.comp_assoc,
      productRestriction_comp_leftMap, BoundedAlgHom.comp_assoc,
      ← a.restriction_comp p.1 q.1 r.1 hpq.1 hqr.1]
  · rw [productRestriction_comp_rightMap, BoundedAlgHom.comp_assoc,
      productRestriction_comp_rightMap, ← BoundedAlgHom.comp_assoc,
      productRestriction_comp_rightMap, BoundedAlgHom.comp_assoc,
      ← b.restriction_comp p.2 q.2 r.2 hpq.2 hqr.2]

/-- The image of a product chart restriction is the product locus. -/
theorem range_productRestriction (p q : a.Index × b.Index) (h : ProductSub a b p q) :
    Set.range (BanachSpectrum.comap (productRestriction a b p q h).toBoundedRingHom) =
      ((a.restrictionDomain p.1 q.1 h.1).product (b.restrictionDomain p.2 q.2 h.2)).locus :=
  (Domain.represents_productBaseMap _ _).2.1

theorem represents_productRestriction (p q : a.Index × b.Index) (h : ProductSub a b p q) :
    Represents K (productRestriction a b p q h)
      (Set.range (BanachSpectrum.comap (productRestriction a b p q h).toBoundedRingHom)) := by
  rw [range_productRestriction]
  exact Domain.represents_productBaseMap _ _

/-- The first projection of a point of a product chart, as a point of the first
chart. -/
def leftPoint (p : a.Index × b.Index) (t : BanachSpectrum (productAlgebra a b p)) :
    BanachSpectrum (a.algebra p.1) :=
  BanachSpectrum.comap (AffinoidCoproduct.leftMap K (a.algebra p.1) (b.algebra p.2)).toBoundedRingHom t

/-- The second projection of a point of a product chart. -/
def rightPoint (p : a.Index × b.Index) (t : BanachSpectrum (productAlgebra a b p)) :
    BanachSpectrum (b.algebra p.2) :=
  BanachSpectrum.comap (AffinoidCoproduct.rightMap K (a.algebra p.1) (b.algebra p.2)).toBoundedRingHom t

theorem leftPoint_pull (p q : a.Index × b.Index) (h : ProductSub a b p q)
    (s : BanachSpectrum (productAlgebra a b p)) :
    leftPoint a b q (BanachSpectrum.comap (productRestriction a b p q h).toBoundedRingHom s) =
      BanachSpectrum.comap (a.restriction p.1 q.1 h.1).toBoundedRingHom (leftPoint a b p s) := by
  apply BanachSpectrum.ext
  intro c
  exact congrArg (fun f : BoundedAlgHom K (a.algebra q.1) (productAlgebra a b p) => s (f c))
    (productRestriction_comp_leftMap a b p q h)

theorem rightPoint_pull (p q : a.Index × b.Index) (h : ProductSub a b p q)
    (s : BanachSpectrum (productAlgebra a b p)) :
    rightPoint a b q (BanachSpectrum.comap (productRestriction a b p q h).toBoundedRingHom s) =
      BanachSpectrum.comap (b.restriction p.2 q.2 h.2).toBoundedRingHom (rightPoint a b p s) := by
  apply BanachSpectrum.ext
  intro c
  exact congrArg (fun f : BoundedAlgHom K (b.algebra q.2) (productAlgebra a b p) => s (f c))
    (productRestriction_comp_rightMap a b p q h)

/-- A point of a product chart lies in the image of a subchart exactly when its
two projections lie in the corresponding chart ranges. -/
theorem mem_range_productRestriction_iff (p q : a.Index × b.Index) (h : ProductSub a b p q)
    (t : BanachSpectrum (productAlgebra a b q)) :
    t ∈ Set.range (BanachSpectrum.comap (productRestriction a b p q h).toBoundedRingHom) ↔
      a.chart q.1 (leftPoint a b q t) ∈ Set.range (a.chart p.1) ∧
        b.chart q.2 (rightPoint a b q t) ∈ Set.range (b.chart p.2) := by
  rw [range_productRestriction]
  rfl

/-- The chart system of the product of two atlases. -/
abbrev productChartSystem : AffinoidChartSystem.{u, max w w'} K where
  Index := a.Index × b.Index
  algebra := productAlgebra a b
  Sub := ProductSub a b
  restriction := productRestriction a b
  sub_refl _ := ⟨subset_rfl, subset_rfl⟩
  sub_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  restriction_refl := productRestriction_refl a b
  restriction_trans := productRestriction_trans a b
  represents := represents_productRestriction a b
  meet := by
    intro p q r hpr hqr t htp htq
    rw [mem_range_productRestriction_iff] at htp htq
    obtain ⟨m₁, hm₁, hx₁⟩ := exists_chart_inter htp.1 htq.1
    obtain ⟨m₂, hm₂, hx₂⟩ := exists_chart_inter (a := b) htp.2 htq.2
    refine ⟨(m₁, m₂), ⟨hm₁.trans Set.inter_subset_left, hm₂.trans Set.inter_subset_left⟩,
      ⟨hm₁.trans Set.inter_subset_right, hm₂.trans Set.inter_subset_right⟩, ?_⟩
    rw [mem_range_productRestriction_iff]
    exact ⟨hx₁, hx₂⟩

theorem chart_leftPoint_pull (p q : a.Index × b.Index) (h : ProductSub a b p q)
    (s : BanachSpectrum (productAlgebra a b p)) :
    a.chart q.1 (leftPoint a b q
      (BanachSpectrum.comap (productRestriction a b p q h).toBoundedRingHom s)) =
        a.chart p.1 (leftPoint a b p s) := by
  rw [leftPoint_pull]
  exact a.restriction_chart p.1 q.1 h.1 _

theorem chart_rightPoint_pull (p q : a.Index × b.Index) (h : ProductSub a b p q)
    (s : BanachSpectrum (productAlgebra a b p)) :
    b.chart q.2 (rightPoint a b q
      (BanachSpectrum.comap (productRestriction a b p q h).toBoundedRingHom s)) =
        b.chart p.2 (rightPoint a b p s) := by
  rw [rightPoint_pull]
  exact b.restriction_chart p.2 q.2 h.2 _

/-- The first projection from the glued product to the first space. -/
def productFst : (productChartSystem a b).Space → X :=
  Quotient.lift (fun z => a.chart z.1.1 (leftPoint a b z.1 z.2)) (by
    rintro ⟨p, s⟩ ⟨q, t⟩ ⟨k, hkp, hkq, v, hvs, hvt⟩
    change a.chart p.1 (leftPoint a b p s) = a.chart q.1 (leftPoint a b q t)
    have hvs' : (productChartSystem a b).pull hkp v = s := hvs
    have hvt' : (productChartSystem a b).pull hkq v = t := hvt
    rw [← hvs', ← hvt']
    exact (chart_leftPoint_pull a b k p hkp v).trans (chart_leftPoint_pull a b k q hkq v).symm)

/-- The second projection from the glued product to the second space. -/
def productSnd : (productChartSystem a b).Space → Y :=
  Quotient.lift (fun z => b.chart z.1.2 (rightPoint a b z.1 z.2)) (by
    rintro ⟨p, s⟩ ⟨q, t⟩ ⟨k, hkp, hkq, v, hvs, hvt⟩
    change b.chart p.2 (rightPoint a b p s) = b.chart q.2 (rightPoint a b q t)
    have hvs' : (productChartSystem a b).pull hkp v = s := hvs
    have hvt' : (productChartSystem a b).pull hkq v = t := hvt
    rw [← hvs', ← hvt']
    exact (chart_rightPoint_pull a b k p hkp v).trans (chart_rightPoint_pull a b k q hkq v).symm)

theorem productFst_chart (p : a.Index × b.Index) (s : BanachSpectrum (productAlgebra a b p)) :
    productFst a b ((productChartSystem a b).chart p s) = a.chart p.1 (leftPoint a b p s) := rfl

theorem productSnd_chart (p : a.Index × b.Index) (s : BanachSpectrum (productAlgebra a b p)) :
    productSnd a b ((productChartSystem a b).chart p s) = b.chart p.2 (rightPoint a b p s) := rfl

theorem continuous_productFst : Continuous (productFst a b) := by
  apply Continuous.quotient_lift
  refine continuous_sigma fun p => ?_
  show Continuous (fun s : BanachSpectrum (productAlgebra a b p) => a.chart p.1 (leftPoint a b p s))
  exact (a.isEmbedding_chart p.1).continuous.comp
    (BanachSpectrum.comapContinuous _).continuous

theorem continuous_productSnd : Continuous (productSnd a b) := by
  apply Continuous.quotient_lift
  refine continuous_sigma fun p => ?_
  show Continuous (fun s : BanachSpectrum (productAlgebra a b p) => b.chart p.2 (rightPoint a b p s))
  exact (b.isEmbedding_chart p.2).continuous.comp
    (BanachSpectrum.comapContinuous _).continuous

variable {a} in
/-- Over a Hausdorff space, the intersection of two chart ranges is covered by
finitely many chart ranges contained in it. -/
theorem exists_finite_charts_inter [T2Space X] (i j : a.Index) :
    ∃ S : Set a.Index, S.Finite ∧
      (∀ m ∈ S, Set.range (a.chart m) ⊆ Set.range (a.chart i) ∩ Set.range (a.chart j)) ∧
      Set.range (a.chart i) ∩ Set.range (a.chart j) ⊆ ⋃ m ∈ S, Set.range (a.chart m) := by
  have hci : IsCompact (Set.range (a.chart i)) :=
    isCompact_range (a.isEmbedding_chart i).continuous
  have hcj : IsCompact (Set.range (a.chart j)) :=
    isCompact_range (a.isEmbedding_chart j).continuous
  obtain ⟨σ, hσ, hστ, hσsub, hcov⟩ := a.isNet_chartFamily.exists_finite_cover_of_subset_inter
    ⟨i, rfl⟩ ⟨j, rfl⟩ (hci.inter_right hcj.isClosed) subset_rfl
  refine ⟨{m | Set.range (a.chart m) ∈ σ}, hσ.preimage a.chartDomain_injective.injOn,
    fun m hm => hσsub _ hm, fun x hx => ?_⟩
  obtain ⟨W, hWσ, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
  obtain ⟨m, rfl⟩ := hστ hWσ
  exact Set.mem_biUnion (show m ∈ {m | Set.range (a.chart m) ∈ σ} from hWσ) hxW

/-- Over Hausdorff spaces, the product chart system has finite overlaps. -/
theorem productChartSystem_hasFiniteOverlaps [T2Space X] [T2Space Y] :
    (productChartSystem a b).HasFiniteOverlaps := by
  intro p q
  obtain ⟨S₁, hS₁, hS₁sub, hS₁cov⟩ := exists_finite_charts_inter p.1 q.1
  obtain ⟨S₂, hS₂, hS₂sub, hS₂cov⟩ := exists_finite_charts_inter (a := b) p.2 q.2
  let C := productChartSystem a b
  refine ⟨{k | k.1.1 ∈ S₁ ∧ k.1.2 ∈ S₂},
    ((hS₁.prod hS₂).preimage Subtype.val_injective.injOn).subset fun k hk => hk, ?_⟩
  intro s t hst
  have hglued := hst
  obtain ⟨k, hkp, hkq, v, hvs, hvt⟩ := hst
  have hcpq : C.chart p s = C.chart q t := C.chart_eq_iff.2 hglued
  have hx₁ : a.chart p.1 (leftPoint a b p s) ∈
      Set.range (a.chart p.1) ∩ Set.range (a.chart q.1) :=
    ⟨⟨_, rfl⟩, ⟨_, (congrArg (productFst a b) hcpq).symm⟩⟩
  have hx₂ : b.chart p.2 (rightPoint a b p s) ∈
      Set.range (b.chart p.2) ∩ Set.range (b.chart q.2) :=
    ⟨⟨_, rfl⟩, ⟨_, (congrArg (productSnd a b) hcpq).symm⟩⟩
  obtain ⟨m₁, hm₁S, hm₁⟩ := Set.mem_iUnion₂.1 (hS₁cov hx₁)
  obtain ⟨m₂, hm₂S, hm₂⟩ := Set.mem_iUnion₂.1 (hS₂cov hx₂)
  have hsubp : ProductSub a b (m₁, m₂) p :=
    ⟨(hS₁sub m₁ hm₁S).trans Set.inter_subset_left, (hS₂sub m₂ hm₂S).trans Set.inter_subset_left⟩
  have hsubq : ProductSub a b (m₁, m₂) q :=
    ⟨(hS₁sub m₁ hm₁S).trans Set.inter_subset_right,
      (hS₂sub m₂ hm₂S).trans Set.inter_subset_right⟩
  have hsr : s ∈ Set.range (BanachSpectrum.comap
      (productRestriction a b (m₁, m₂) p hsubp).toBoundedRingHom) :=
    (mem_range_productRestriction_iff a b (m₁, m₂) p hsubp s).2 ⟨hm₁, hm₂⟩
  obtain ⟨v', hv'⟩ := hsr
  refine ⟨⟨(m₁, m₂), hsubp, hsubq⟩, ⟨hm₁S, hm₂S⟩, v', hv', ?_⟩
  apply C.chart_injective q
  have h1 : C.chart q (C.pull hsubq v') = C.chart (m₁, m₂) v' := C.chart_pull hsubq v'
  have h2 : C.chart p (C.pull hsubp v') = C.chart (m₁, m₂) v' := C.chart_pull hsubp v'
  have h3 : C.pull hsubp v' = s := hv'
  rw [h3] at h2
  exact h1.trans (h2.symm.trans hcpq)

/-- Over Hausdorff spaces, the product charts are closed embeddings. -/
theorem isClosedEmbedding_productChart [T2Space X] [T2Space Y] (p : a.Index × b.Index) :
    IsClosedEmbedding ((productChartSystem a b).chart p) :=
  (productChartSystem a b).isClosedEmbedding_chart (productChartSystem_hasFiniteOverlaps a b) p

end IndexedAffinoidAtlas

end Langlands.Analytic
