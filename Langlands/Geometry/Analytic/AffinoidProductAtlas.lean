import Langlands.Geometry.Analytic.AffinoidProductChartSystem
import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections
import Langlands.Geometry.Analytic.FullRecognitionPairSystems

/-! # The affinoid atlas of the product of two Hausdorff analytic spaces -/

noncomputable section

universe u v v' w w'

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra
open scoped Topology

namespace AtlasTopology

variable {Z : Type*} {X : Type*} {Y : Type*}
  [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]

/-- The nonempty intersections of a preimage of a member of `τ` under `f` with
a preimage of a member of `υ` under `g`. -/
def preimageProductFamily (f : Z → X) (g : Z → Y) (τ : Set (Set X))
    (υ : Set (Set Y)) : Set (Set Z) :=
  {W | W.Nonempty ∧ ∃ U ∈ τ, ∃ V ∈ υ, W = f ⁻¹' U ∩ g ⁻¹' V}

variable {f : Z → X} {g : Z → Y} {τ : Set (Set X)} {υ : Set (Set Y)}

/-- Preimage intersections of two quasinets along continuous maps form a
quasinet. -/
theorem IsQuasinet.preimageProductFamily (hf : Continuous f) (hg : Continuous g)
    (hτ : IsQuasinet τ) (hυ : IsQuasinet υ) :
    IsQuasinet (AtlasTopology.preimageProductFamily f g τ υ) := by
  intro z
  obtain ⟨σ, hσ, hστ, hσz, hσN⟩ := hτ (f z)
  obtain ⟨σ', hσ', hσυ, hσz', hσN'⟩ := hυ (g z)
  refine ⟨Set.image2 (fun U V => f ⁻¹' U ∩ g ⁻¹' V) σ σ', hσ.image2 _ hσ', ?_, ?_, ?_⟩
  · rintro _ ⟨U, hU, V, hV, rfl⟩
    exact ⟨⟨z, hσz U hU, hσz' V hV⟩, U, hστ hU, V, hσυ hV, rfl⟩
  · rintro _ ⟨U, hU, V, hV, rfl⟩
    exact ⟨hσz U hU, hσz' V hV⟩
  · refine Filter.mem_of_superset (Filter.inter_mem (hf.continuousAt.preimage_mem_nhds hσN)
      (hg.continuousAt.preimage_mem_nhds hσN')) ?_
    rintro y ⟨⟨U, hU, hyU⟩, ⟨V, hV, hyV⟩⟩
    exact ⟨_, ⟨U, hU, V, hV, rfl⟩, hyU, hyV⟩

/-- Relative finite neighborhood refinements of two subspaces give one of the
intersection of their preimages. -/
theorem locallyRefines_preimageProductFamily (hf : Continuous f) (hg : Continuous g)
    {S : Set X} {T : Set Y} (hS : LocallyRefines τ {S}) (hT : LocallyRefines υ {T}) :
    LocallyRefines (AtlasTopology.preimageProductFamily f g τ υ) {f ⁻¹' S ∩ g ⁻¹' T} := by
  intro W hW z hz
  rcases mem_singleton_iff.mp hW with rfl
  obtain ⟨σ, hσ, hστ, hσS, hσN⟩ := hS S (mem_singleton S) (f z) hz.1
  obtain ⟨σ', hσ', hσυ, hσT, hσN'⟩ := hT T (mem_singleton T) (g z) hz.2
  refine ⟨Set.image2 (fun U V => f ⁻¹' U ∩ g ⁻¹' V) σ σ', hσ.image2 _ hσ', ?_, ?_, ?_⟩
  · rintro _ ⟨U, hU, V, hV, rfl⟩
    exact ⟨⟨z, (hσS U hU).2, (hσT V hV).2⟩, U, hστ hU, V, hσυ hV, rfl⟩
  · rintro _ ⟨U, hU, V, hV, rfl⟩
    exact ⟨inter_subset_inter (preimage_mono (hσS U hU).1) (preimage_mono (hσT V hV).1),
      (hσS U hU).2, (hσT V hV).2⟩
  · have h₁ : f ⁻¹' ⋃₀ σ ∈ 𝓝[f ⁻¹' S ∩ g ⁻¹' T] z :=
      hf.continuousWithinAt.tendsto_nhdsWithin (fun _ hy => hy.1) hσN
    have h₂ : g ⁻¹' ⋃₀ σ' ∈ 𝓝[f ⁻¹' S ∩ g ⁻¹' T] z :=
      hg.continuousWithinAt.tendsto_nhdsWithin (fun _ hy => hy.2) hσN'
    refine Filter.mem_of_superset (Filter.inter_mem h₁ h₂) ?_
    rintro y ⟨⟨U, hU, hyU⟩, ⟨V, hV, hyV⟩⟩
    exact ⟨_, ⟨U, hU, V, hV, rfl⟩, hyU, hyV⟩

/-- Preimage intersections of two nets along continuous maps form a net. -/
theorem IsNet.preimageProductFamily (hf : Continuous f) (hg : Continuous g)
    (hτ : IsNet τ) (hυ : IsNet υ) :
    IsNet (AtlasTopology.preimageProductFamily f g τ υ) := by
  refine ⟨hτ.1.preimageProductFamily hf hg hυ.1, ?_⟩
  rintro _ ⟨-, U₁, hU₁, V₁, hV₁, rfl⟩ _ ⟨-, U₂, hU₂, V₂, hV₂, rfl⟩
  have heq : (f ⁻¹' U₁ ∩ g ⁻¹' V₁) ∩ (f ⁻¹' U₂ ∩ g ⁻¹' V₂) =
      f ⁻¹' (U₁ ∩ U₂) ∩ g ⁻¹' (V₁ ∩ V₂) := by
    ext z
    simp only [mem_inter_iff, mem_preimage]
    tauto
  rw [heq, isQuasinet_restrictedFamily_iff]
  exact locallyRefines_preimageProductFamily hf hg
    ((isQuasinet_restrictedFamily_iff τ _).1 (hτ.2 U₁ hU₁ U₂ hU₂))
    ((isQuasinet_restrictedFamily_iff υ _).1 (hυ.2 V₁ hV₁ V₂ hV₂))

end AtlasTopology

/-- A space is Hausdorff if any two distinct points are separated by open sets
or lie in a common open Hausdorff subspace. -/
theorem t2Space_of_separated_or_open_t2 {Z : Type*} [TopologicalSpace Z]
    (h : ∀ z z' : Z, z ≠ z' →
      (∃ U V : Set Z, IsOpen U ∧ IsOpen V ∧ z ∈ U ∧ z' ∈ V ∧ Disjoint U V) ∨
        ∃ N : Set Z, IsOpen N ∧ z ∈ N ∧ z' ∈ N ∧ T2Space N) : T2Space Z := by
  refine ⟨fun z z' hne => ?_⟩
  rcases h z z' hne with hsep | ⟨N, hN, hz, hz', hT⟩
  · exact hsep
  · obtain ⟨U, V, hU, hV, hzU, hzV, hUV⟩ :=
      t2_separation (x := (⟨z, hz⟩ : N)) (y := ⟨z', hz'⟩)
        fun h => hne (congrArg Subtype.val h)
    exact ⟨Subtype.val '' U, Subtype.val '' V, hN.isOpenMap_subtype_val U hU,
      hN.isOpenMap_subtype_val V hV, ⟨_, hzU, rfl⟩, ⟨_, hzV, rfl⟩,
      (Set.disjoint_image_iff Subtype.val_injective).2 hUV⟩

namespace PresentedAffinoidAlgebra.AffinoidCoproduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The constructed scalar presentation has exactly one spectrum point: every
element is a scalar, and every point restricts to the norm on scalars. -/
instance : Subsingleton (BanachSpectrum (initialAlgebra K)) := by
  refine ⟨fun x y => BanachSpectrum.ext fun z => ?_⟩
  have hz : scalarInclusion K (initialMap K K z) = z :=
    congrArg (fun f : BoundedAlgHom K (initialAlgebra K) (initialAlgebra K) => f z)
      (initial_hom_ext K (initialAlgebra K) ((scalarInclusion K).comp (initialMap K K))
        (BoundedAlgHom.id K (initialAlgebra K)))
  rw [← hz]
  change x (algebraMap K (initialAlgebra K) (initialMap K K z)) =
    y (algebraMap K (initialAlgebra K) (initialMap K K z))
  rw [BanachSpectrum.algebraMap_apply, BanachSpectrum.algebraMap_apply]

/-- Any two points of the factors are the projections of one point of the
actual affinoid coproduct. -/
theorem exists_point (A B : PresentedAffinoidAlgebra K) (x : BanachSpectrum A)
    (y : BanachSpectrum B) :
    ∃ z : BanachSpectrum (algebra K A B),
      BanachSpectrum.comap (leftMap K A B).toBoundedRingHom z = x ∧
        BanachSpectrum.comap (rightMap K A B).toBoundedRingHom z = y :=
  AffinoidPushout.exists_point (initialMap K A) (initialMap K B) x y (Subsingleton.elim _ _)

end PresentedAffinoidAlgebra.AffinoidCoproduct

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {Y : Type v'} [TopologicalSpace Y]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) (b : IndexedAffinoidAtlas.{u, v', w'} K Y)

/-- Two points of the factor charts are the projections of a point of the
product chart. -/
theorem exists_productPoint (p : a.Index × b.Index) (x : BanachSpectrum (a.algebra p.1))
    (y : BanachSpectrum (b.algebra p.2)) :
    ∃ t, leftPoint a b p t = x ∧ rightPoint a b p t = y :=
  AffinoidCoproduct.exists_point _ _ x y

/-- A point of the glued product lies in a product chart exactly when its two
projections lie in the two factor charts. -/
theorem mem_range_productChart_iff (p : a.Index × b.Index)
    (z : (productChartSystem a b).Space) :
    z ∈ range ((productChartSystem a b).chart p) ↔
      productFst a b z ∈ range (a.chart p.1) ∧ productSnd a b z ∈ range (b.chart p.2) := by
  let C := productChartSystem a b
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨_, (productFst_chart a b p s).symm⟩, ⟨_, (productSnd_chart a b p s).symm⟩⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨q, t, rfl⟩ := C.exists_chart z
    rw [productFst_chart] at hx
    rw [productSnd_chart] at hy
    obtain ⟨m₁, hm₁, hx₁⟩ := exists_chart_inter hx ⟨_, rfl⟩
    obtain ⟨m₂, hm₂, hy₂⟩ := exists_chart_inter (a := b) hy ⟨_, rfl⟩
    have hq : ProductSub a b (m₁, m₂) q :=
      ⟨hm₁.trans inter_subset_right, hm₂.trans inter_subset_right⟩
    have hp : ProductSub a b (m₁, m₂) p :=
      ⟨hm₁.trans inter_subset_left, hm₂.trans inter_subset_left⟩
    obtain ⟨v, hv⟩ := (mem_range_productRestriction_iff a b (m₁, m₂) q hq t).2 ⟨hx₁, hy₂⟩
    refine ⟨C.pull hp v, ?_⟩
    have hv' : C.pull hq v = t := hv
    rw [C.chart_pull hp v, ← C.chart_pull hq v, hv']

/-- The range of a product chart is the intersection of the preimages of the
two factor chart ranges. -/
theorem range_productChart (p : a.Index × b.Index) :
    range ((productChartSystem a b).chart p) =
      productFst a b ⁻¹' range (a.chart p.1) ∩ productSnd a b ⁻¹' range (b.chart p.2) :=
  Set.ext fun z => mem_range_productChart_iff a b p z

/-- Product chart inclusions give inclusions of chart ranges. -/
theorem range_productChart_subset {p q : a.Index × b.Index} (h : ProductSub a b p q) :
    range ((productChartSystem a b).chart p) ⊆ range ((productChartSystem a b).chart q) := by
  rintro _ ⟨s, rfl⟩
  exact ⟨(productChartSystem a b).pull h s, (productChartSystem a b).chart_pull h s⟩

/-- Pairs of charts whose two chart domains are both nonempty. These index the
atlas of the product. -/
abbrev ProductIndex : Type (max w w') :=
  {p : a.Index × b.Index // (range (a.chart p.1)).Nonempty ∧ (range (b.chart p.2)).Nonempty}

/-- A product chart with nonempty factors is nonempty. -/
theorem range_productChart_nonempty (p : ProductIndex a b) :
    (range ((productChartSystem a b).chart p.1)).Nonempty := by
  obtain ⟨_, x, rfl⟩ := p.2.1
  obtain ⟨_, y, rfl⟩ := p.2.2
  obtain ⟨t, -, -⟩ := exists_productPoint a b p.1 x y
  exact ⟨_, t, rfl⟩

/-- For nonempty factors, an inclusion of product chart ranges is a
componentwise inclusion of factor chart ranges. -/
theorem productSub_of_range_subset (p : ProductIndex a b) (q : a.Index × b.Index)
    (h : range ((productChartSystem a b).chart p.1) ⊆
      range ((productChartSystem a b).chart q)) :
    ProductSub a b p.1 q := by
  constructor
  · rintro _ ⟨x, rfl⟩
    obtain ⟨_, y, rfl⟩ := p.2.2
    obtain ⟨t, ht, -⟩ := exists_productPoint a b p.1 x y
    have hq := (mem_range_productChart_iff a b q _).1 (h ⟨t, rfl⟩)
    rw [productFst_chart, ht] at hq
    exact hq.1
  · rintro _ ⟨y, rfl⟩
    obtain ⟨_, x, rfl⟩ := p.2.1
    obtain ⟨t, -, ht⟩ := exists_productPoint a b p.1 x y
    have hq := (mem_range_productChart_iff a b q _).1 (h ⟨t, rfl⟩)
    rw [productSnd_chart, ht] at hq
    exact hq.2

/-- The product chart family is the family of nonempty intersections of
preimages of factor chart ranges under the two projections. -/
theorem productChartFamily_eq :
    range (fun p : ProductIndex a b => range ((productChartSystem a b).chart p.1)) =
      AtlasTopology.preimageProductFamily (productFst a b) (productSnd a b)
        (range fun i => range (a.chart i)) (range fun j => range (b.chart j)) := by
  ext W
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨range_productChart_nonempty a b p, _, ⟨p.1.1, rfl⟩, _, ⟨p.1.2, rfl⟩,
      range_productChart a b p.1⟩
  · rintro ⟨⟨z, hz⟩, _, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact ⟨⟨(i, j), ⟨_, hz.1⟩, ⟨_, hz.2⟩⟩, range_productChart a b (i, j)⟩

/-- The product chart ranges form a net on the glued product. -/
theorem isNet_productChartFamily :
    AtlasTopology.IsNet
      (range fun p : ProductIndex a b => range ((productChartSystem a b).chart p.1)) := by
  rw [productChartFamily_eq]
  exact AtlasTopology.IsNet.preimageProductFamily (continuous_productFst a b)
    (continuous_productSnd a b) a.isNet_chartFamily b.isNet_chartFamily

/-- The glued product of two Hausdorff spaces with affinoid atlases is
Hausdorff. -/
theorem t2Space_productSpace [T2Space X] [T2Space Y] :
    T2Space (productChartSystem a b).Space := by
  let C := productChartSystem a b
  apply t2Space_of_separated_or_open_t2
  intro z z' hne
  by_cases hx : productFst a b z = productFst a b z'
  · by_cases hy : productSnd a b z = productSnd a b z'
    · right
      obtain ⟨σ, hσ, hστ, -, hσN⟩ := a.isNet_chartFamily.1 (productFst a b z)
      obtain ⟨σ', hσ', hστ', -, hσN'⟩ := b.isNet_chartFamily.1 (productSnd a b z)
      let F : Set C.Space := productFst a b ⁻¹' ⋃₀ σ ∩ productSnd a b ⁻¹' ⋃₀ σ'
      let N : Set C.Space :=
        productFst a b ⁻¹' interior (⋃₀ σ) ∩ productSnd a b ⁻¹' interior (⋃₀ σ')
      have hNF : N ⊆ F :=
        inter_subset_inter (preimage_mono interior_subset) (preimage_mono interior_subset)
      have hF : T2Space F := by
        have : Finite ↥(σ ×ˢ σ') := (hσ.prod hσ').to_subtype
        refine t2Space_of_finite_isClosed_cover
          (fun k : ↥(σ ×ˢ σ') =>
            (Subtype.val ⁻¹' (productFst a b ⁻¹' k.1.1 ∩ productSnd a b ⁻¹' k.1.2) : Set F))
          ?_ ?_ ?_
        · intro k
          obtain ⟨i, hi⟩ := hστ k.2.1
          obtain ⟨j, hj⟩ := hστ' k.2.2
          have hi' : range (a.chart i) = k.1.1 := hi
          have hj' : range (b.chart j) = k.1.2 := hj
          refine IsClosed.preimage continuous_subtype_val (IsClosed.inter ?_ ?_)
          · rw [← hi']
            exact (isCompact_range (a.isEmbedding_chart i).continuous).isClosed.preimage
              (continuous_productFst a b)
          · rw [← hj']
            exact (isCompact_range (b.isEmbedding_chart j).continuous).isClosed.preimage
              (continuous_productSnd a b)
        · intro k
          obtain ⟨i, hi⟩ := hστ k.2.1
          obtain ⟨j, hj⟩ := hστ' k.2.2
          have hi' : range (a.chart i) = k.1.1 := hi
          have hj' : range (b.chart j) = k.1.2 := hj
          have : T2Space (range (C.chart (i, j))) :=
            (isClosedEmbedding_productChart a b (i, j)).isEmbedding.toHomeomorph.t2Space
          have hmem : ∀ w : (Subtype.val ⁻¹'
              (productFst a b ⁻¹' k.1.1 ∩ productSnd a b ⁻¹' k.1.2) : Set F),
              (w : F).1 ∈ range (C.chart (i, j)) := by
            intro w
            rw [range_productChart]
            refine ⟨?_, ?_⟩
            · change productFst a b (w : F).1 ∈ range (a.chart i)
              rw [hi']
              exact w.2.1
            · change productSnd a b (w : F).1 ∈ range (b.chart j)
              rw [hj']
              exact w.2.2
          refine T2Space.of_injective_continuous
            (f := fun w => (⟨(w : F).1, hmem w⟩ : range (C.chart (i, j)))) ?_ ?_
          · intro w w' hww'
            have h := congrArg (Subtype.val : range (C.chart (i, j)) → C.Space) hww'
            exact Subtype.ext (Subtype.ext h)
          · exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
        · intro w
          obtain ⟨U, hU, hwU⟩ := w.2.1
          obtain ⟨V, hV, hwV⟩ := w.2.2
          exact ⟨⟨(U, V), hU, hV⟩, hwU, hwV⟩
      refine ⟨N, ?_, ?_, ?_, ?_⟩
      · exact (isOpen_interior.preimage (continuous_productFst a b)).inter
          (isOpen_interior.preimage (continuous_productSnd a b))
      · exact ⟨mem_interior_iff_mem_nhds.2 hσN, mem_interior_iff_mem_nhds.2 hσN'⟩
      · refine ⟨?_, ?_⟩
        · change productFst a b z' ∈ interior (⋃₀ σ)
          rw [← hx]
          exact mem_interior_iff_mem_nhds.2 hσN
        · change productSnd a b z' ∈ interior (⋃₀ σ')
          rw [← hy]
          exact mem_interior_iff_mem_nhds.2 hσN'
      · exact T2Space.of_injective_continuous (f := Set.inclusion hNF)
          (Set.inclusion_injective hNF) (continuous_inclusion hNF)
    · left
      obtain ⟨U, V, hU, hV, hzU, hzV, hUV⟩ := t2_separation hy
      exact ⟨productSnd a b ⁻¹' U, productSnd a b ⁻¹' V,
        hU.preimage (continuous_productSnd a b), hV.preimage (continuous_productSnd a b),
        hzU, hzV, hUV.preimage _⟩
  · left
    obtain ⟨U, V, hU, hV, hzU, hzV, hUV⟩ := t2_separation hx
    exact ⟨productFst a b ⁻¹' U, productFst a b ⁻¹' V,
      hU.preimage (continuous_productFst a b), hV.preimage (continuous_productFst a b),
      hzU, hzV, hUV.preimage _⟩

/-- The indexed affinoid atlas of the glued product of two Hausdorff spaces.
Its charts are the product charts with nonempty factors, its algebras the
affinoid coproducts of the factor chart algebras, and its restrictions the
coproducts of the factor restrictions. -/
def productAtlas [T2Space X] [T2Space Y] :
    IndexedAffinoidAtlas.{u, max u w w', max w w'} K (productChartSystem a b).Space where
  Index := ProductIndex a b
  algebra p := productAlgebra a b p.1
  chart p := (productChartSystem a b).chart p.1
  isEmbedding_chart p := (isClosedEmbedding_productChart a b p.1).isEmbedding
  chartDomain_injective := by
    intro p q h
    have h' : range ((productChartSystem a b).chart p.1) =
        range ((productChartSystem a b).chart q.1) := h
    have h₁ := productSub_of_range_subset a b p q.1 h'.subset
    have h₂ := productSub_of_range_subset a b q p.1 h'.symm.subset
    exact Subtype.ext (Prod.ext (a.chartDomain_injective (h₁.1.antisymm h₂.1))
      (b.chartDomain_injective (h₁.2.antisymm h₂.2)))
  locallyHausdorff _ := by
    have := t2Space_productSpace a b
    exact ⟨univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := isNet_productChartFamily a b
  restriction p q h := productRestriction a b p.1 q.1 (productSub_of_range_subset a b p q.1 h)
  restriction_chart p q h x :=
    (productChartSystem a b).chart_pull (productSub_of_range_subset a b p q.1 h) x
  restriction_universal p q h R φ hφ := by
    apply (represents_productRestriction a b p.1 q.1 _).2.2 R φ
    intro x
    have hx := (mem_range_productChart_iff a b p.1 _).1 (hφ x)
    rw [productFst_chart, productSnd_chart] at hx
    exact (mem_range_productRestriction_iff a b p.1 q.1 _ _).2 hx
  restriction_id p _ := productRestriction_refl a b p.1
  restriction_comp p q r hpq hqr _ :=
    productRestriction_trans a b (productSub_of_range_subset a b p q.1 hpq)
      (productSub_of_range_subset a b q r.1 hqr)

/-- The atlas presentation of the product of two Hausdorff spaces with
affinoid atlases. -/
def productPresentation [T2Space X] [T2Space Y] :
    AffinoidAtlasPresentation.{u, max u w w', max w w'} K where
  space := TopCat.of (productChartSystem a b).Space
  atlas := productAtlas a b

/-- The first projection maps a product chart with nonempty factors onto the
first factor chart. -/
theorem productFst_image_range (p : ProductIndex a b) :
    productFst a b '' range ((productChartSystem a b).chart p.1) = range (a.chart p.1.1) := by
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, (productFst_chart a b p.1 t).symm⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨_, y, rfl⟩ := p.2.2
    obtain ⟨t, ht, -⟩ := exists_productPoint a b p.1 x y
    exact ⟨_, ⟨t, rfl⟩, by rw [productFst_chart, ht]⟩

/-- The second projection maps a product chart with nonempty factors onto the
second factor chart. -/
theorem productSnd_image_range (p : ProductIndex a b) :
    productSnd a b '' range ((productChartSystem a b).chart p.1) = range (b.chart p.1.2) := by
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, (productSnd_chart a b p.1 t).symm⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨_, x, rfl⟩ := p.2.1
    obtain ⟨t, -, ht⟩ := exists_productPoint a b p.1 x y
    exact ⟨_, ⟨t, rfl⟩, by rw [productSnd_chart, ht]⟩

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

open IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : AffinoidAtlasPresentation.{u, v, w} K) (Q : AffinoidAtlasPresentation.{u, v', w'} K)
  [T2Space P.space] [T2Space Q.space]

/-- The product presentation of two Hausdorff atlas presentations. -/
abbrev product : AffinoidAtlasPresentation.{u, max u w w', max w w'} K :=
  productPresentation P.atlas Q.atlas

/-- The first projection as a system of bounded maps on all admissible chart
pairs. On a product chart and an admissible first-factor chart it is the
first coproduct leg after the first-factor restriction. -/
def productFst : AdmissiblePairSystem (product P Q) P where
  baseMap := ⟨IndexedAffinoidAtlas.productFst P.atlas Q.atlas,
    continuous_productFst P.atlas Q.atlas⟩
  pullback p i h :=
    (AffinoidCoproduct.leftMap K (P.atlas.algebra p.1.1) (Q.atlas.algebra p.1.2)).comp
      (P.atlas.restriction p.1.1 i ((productFst_image_range P.atlas Q.atlas p).symm.subset.trans h))
  chart_comm p i h x := by
    change P.atlas.chart i (BanachSpectrum.comap
      (P.atlas.restriction p.1.1 i _).toBoundedRingHom (leftPoint P.atlas Q.atlas p.1 x)) =
        P.atlas.chart p.1.1 (leftPoint P.atlas Q.atlas p.1 x)
    exact P.atlas.restriction_chart _ _ _ _
  restriction_comm p p' i i' hp hi h h' := by
    have hsub := productSub_of_range_subset P.atlas Q.atlas p p'.1 hp
    have hpi : range (P.atlas.chart p.1.1) ⊆ range (P.atlas.chart i) :=
      (productFst_image_range P.atlas Q.atlas p).symm.subset.trans h
    have hpi' : range (P.atlas.chart p'.1.1) ⊆ range (P.atlas.chart i') :=
      (productFst_image_range P.atlas Q.atlas p').symm.subset.trans h'
    have hr := P.atlas.restriction_comp p.1.1 p'.1.1 i' hsub.1 hpi' (hpi.trans hi)
    have hr' := P.atlas.restriction_comp p.1.1 i i' hpi hi (hpi.trans hi)
    have hl := productRestriction_comp_leftMap P.atlas Q.atlas p.1 p'.1 hsub
    show (productRestriction P.atlas Q.atlas p.1 p'.1 hsub).comp
        ((AffinoidCoproduct.leftMap K _ _).comp (P.atlas.restriction p'.1.1 i' hpi')) =
      ((AffinoidCoproduct.leftMap K _ _).comp (P.atlas.restriction p.1.1 i hpi)).comp
        (P.atlas.restriction i i' hi)
    rw [← BoundedAlgHom.comp_assoc, hl, BoundedAlgHom.comp_assoc, ← hr,
      BoundedAlgHom.comp_assoc, ← hr']

/-- Every product chart maps into its own first-factor chart. -/
theorem productFst_target_exists (p : (product P Q).atlas.Index) :
    ∃ i, (productFst P Q).baseMap '' Set.range ((product P Q).atlas.chart p) ⊆
      Set.range (P.atlas.chart i) :=
  ⟨p.1.1, (productFst_image_range P.atlas Q.atlas p).subset⟩

/-- The second projection as a system of bounded maps on all admissible chart
pairs. -/
def productSnd : AdmissiblePairSystem (product P Q) Q where
  baseMap := ⟨IndexedAffinoidAtlas.productSnd P.atlas Q.atlas,
    continuous_productSnd P.atlas Q.atlas⟩
  pullback p j h :=
    (AffinoidCoproduct.rightMap K (P.atlas.algebra p.1.1) (Q.atlas.algebra p.1.2)).comp
      (Q.atlas.restriction p.1.2 j ((productSnd_image_range P.atlas Q.atlas p).symm.subset.trans h))
  chart_comm p j h x := by
    change Q.atlas.chart j (BanachSpectrum.comap
      (Q.atlas.restriction p.1.2 j _).toBoundedRingHom (rightPoint P.atlas Q.atlas p.1 x)) =
        Q.atlas.chart p.1.2 (rightPoint P.atlas Q.atlas p.1 x)
    exact Q.atlas.restriction_chart _ _ _ _
  restriction_comm p p' j j' hp hj h h' := by
    have hsub := productSub_of_range_subset P.atlas Q.atlas p p'.1 hp
    have hpj : range (Q.atlas.chart p.1.2) ⊆ range (Q.atlas.chart j) :=
      (productSnd_image_range P.atlas Q.atlas p).symm.subset.trans h
    have hpj' : range (Q.atlas.chart p'.1.2) ⊆ range (Q.atlas.chart j') :=
      (productSnd_image_range P.atlas Q.atlas p').symm.subset.trans h'
    have hr := Q.atlas.restriction_comp p.1.2 p'.1.2 j' hsub.2 hpj' (hpj.trans hj)
    have hr' := Q.atlas.restriction_comp p.1.2 j j' hpj hj (hpj.trans hj)
    have hl := productRestriction_comp_rightMap P.atlas Q.atlas p.1 p'.1 hsub
    show (productRestriction P.atlas Q.atlas p.1 p'.1 hsub).comp
        ((AffinoidCoproduct.rightMap K _ _).comp (Q.atlas.restriction p'.1.2 j' hpj')) =
      ((AffinoidCoproduct.rightMap K _ _).comp (Q.atlas.restriction p.1.2 j hpj)).comp
        (Q.atlas.restriction j j' hj)
    rw [← BoundedAlgHom.comp_assoc, hl, BoundedAlgHom.comp_assoc, ← hr,
      BoundedAlgHom.comp_assoc, ← hr']

/-- Every product chart maps into its own second-factor chart. -/
theorem productSnd_target_exists (p : (product P Q).atlas.Index) :
    ∃ j, (productSnd P Q).baseMap '' Set.range ((product P Q).atlas.chart p) ⊆
      Set.range (Q.atlas.chart j) :=
  ⟨p.1.2, (productSnd_image_range P.atlas Q.atlas p).subset⟩

end AffinoidAtlasPresentation

end Langlands.Analytic
