import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms

/-! # Local Hausdorffness of preimages under finite target families -/

universe u v w

open Set Topology

namespace Langlands.Analytic.TargetLocalHausdorff

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Ambient separation of two points of a subset by open sets whose
intersection misses the subset makes the subset Hausdorff. -/
theorem t2Space_of_ambient_separation (s : Set X)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ∃ a b : Set X, IsOpen a ∧ IsOpen b ∧ x ∈ a ∧ y ∈ b ∧ a ∩ b ∩ s = ∅) :
    T2Space s := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨a, b, ha, hb, hxa, hyb, hab⟩ :=
    h x x.property y y.property (Subtype.coe_injective.ne hxy)
  refine ⟨Subtype.val ⁻¹' a, Subtype.val ⁻¹' b, ha.preimage continuous_subtype_val,
    hb.preimage continuous_subtype_val, hxa, hyb, ?_⟩
  rw [Set.disjoint_iff]
  intro z hz
  have hz' : (z : X) ∈ a ∩ b ∩ s := ⟨⟨hz.1, hz.2⟩, z.property⟩
  rw [hab] at hz'
  exact hz'

/-- A Hausdorff subset separates any two of its distinct points by ambient
open sets whose intersection misses the subset. -/
theorem exists_ambient_separation (s : Set X) [T2Space s] {x y : X} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) :
    ∃ a b : Set X, IsOpen a ∧ IsOpen b ∧ x ∈ a ∧ y ∈ b ∧ a ∩ b ∩ s = ∅ := by
  obtain ⟨a', b', ha', hb', hxa', hyb', hab'⟩ :=
    t2_separation (x := (⟨x, hx⟩ : s)) (y := ⟨y, hy⟩) (fun h => hxy (congrArg Subtype.val h))
  obtain ⟨a, ha, rfl⟩ := isOpen_induced_iff.mp ha'
  obtain ⟨b, hb, rfl⟩ := isOpen_induced_iff.mp hb'
  refine ⟨a, b, ha, hb, hxa', hyb', Set.subset_empty_iff.mp ?_⟩
  rintro z ⟨⟨hza, hzb⟩, hzs⟩
  exact Set.disjoint_left.mp hab' (show (⟨z, hzs⟩ : s) ∈ Subtype.val ⁻¹' a from hza) hzb

/-- Target-local Hausdorffness of preimages.  Let `g` be continuous, let `S`
be a Hausdorff subset of the target, and suppose every point `y ∈ S` admits a
finite family of target subsets, all containing `y`, whose union is a
neighborhood of `y`, and whose individual preimages in `V` are Hausdorff.  Then
the preimage of `S` in `V` is Hausdorff. -/
theorem t2Space_inter_preimage {g : X → Y} (hg : Continuous g) (V : Set X) (S : Set Y)
    [T2Space S]
    (hloc : ∀ y ∈ S, ∃ T : Set (Set Y), T.Finite ∧
      (∀ t ∈ T, y ∈ t ∧ T2Space ↥(V ∩ g ⁻¹' t)) ∧ ⋃₀ T ∈ 𝓝 y) :
    T2Space ↥(V ∩ g ⁻¹' S) := by
  apply t2Space_of_ambient_separation
  rintro x₁ ⟨hx₁V, hx₁S⟩ x₂ ⟨hx₂V, hx₂S⟩ hne
  by_cases hg₁₂ : g x₁ = g x₂
  · obtain ⟨T, hTfin, hTmem, hTnhds⟩ := hloc (g x₁) hx₁S
    have hsep : ∀ t ∈ T, ∃ a b : Set X, IsOpen a ∧ IsOpen b ∧ x₁ ∈ a ∧ x₂ ∈ b ∧
        a ∩ b ∩ (V ∩ g ⁻¹' t) = ∅ := by
      intro t ht
      obtain ⟨hyt, hT2⟩ := hTmem t ht
      exact exists_ambient_separation (V ∩ g ⁻¹' t) ⟨hx₁V, hyt⟩
        ⟨hx₂V, show g x₂ ∈ t from hg₁₂ ▸ hyt⟩ hne
    choose! a b ha hb hxa hxb hab using hsep
    let N := interior (⋃₀ T)
    have hN : g x₁ ∈ N := mem_interior_iff_mem_nhds.mpr hTnhds
    refine ⟨(⋂ t ∈ T, a t) ∩ g ⁻¹' N, (⋂ t ∈ T, b t) ∩ g ⁻¹' N,
      (hTfin.isOpen_biInter ha).inter (isOpen_interior.preimage hg),
      (hTfin.isOpen_biInter hb).inter (isOpen_interior.preimage hg),
      ⟨Set.mem_iInter₂.mpr hxa, hN⟩,
      ⟨Set.mem_iInter₂.mpr hxb, show g x₂ ∈ N from hg₁₂ ▸ hN⟩, Set.subset_empty_iff.mp ?_⟩
    rintro z ⟨⟨⟨hza, hzN⟩, ⟨hzb, -⟩⟩, hzV, -⟩
    obtain ⟨t, ht, hzt⟩ := interior_subset hzN
    have hz : z ∈ a t ∩ b t ∩ (V ∩ g ⁻¹' t) :=
      ⟨⟨Set.mem_iInter₂.mp hza t ht, Set.mem_iInter₂.mp hzb t ht⟩, hzV, hzt⟩
    rw [hab t ht] at hz
    exact hz
  · obtain ⟨a, b, ha, hb, hxa, hxb, hab⟩ := exists_ambient_separation S hx₁S hx₂S hg₁₂
    refine ⟨g ⁻¹' a, g ⁻¹' b, ha.preimage hg, hb.preimage hg, hxa, hxb,
      Set.subset_empty_iff.mp ?_⟩
    rintro z ⟨⟨hza, hzb⟩, -, hzS⟩
    have hz : g z ∈ a ∩ b ∩ S := ⟨⟨hza, hzb⟩, hzS⟩
    rw [hab] at hz
    exact hz

end Langlands.Analytic.TargetLocalHausdorff

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Weak form of the target family hypothesis: every member of the family at
`x` contains `x`, and its literal preimage in `V` is the locus of a recognized
source affinoid. -/
theorem t2Space_inter_preimage_of_recognizedFamilies
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : Set A.space) (U : Set B.space)
    (hfam : ∀ x ∈ U, ∃ I : Set B.atlas.saturatedAtlas.RecognizedSubset, I.Finite ∧
      (∀ W ∈ I, x ∈ W.locus ∧
        ∃ P : A.atlas.saturatedAtlas.RecognizedSubset, P.locus = V ∩ g.baseMap ⁻¹' W.locus) ∧
      (⋃ W ∈ I, W.locus) ∈ 𝓝 x)
    (S : Set B.space) [T2Space S] (hS : S ⊆ U) :
    T2Space ↥(V ∩ g.baseMap ⁻¹' S) := by
  refine @TargetLocalHausdorff.t2Space_inter_preimage _ _ _ _ _ g.baseMap.continuous V S
    ‹T2Space S› ?_
  intro y hy
  obtain ⟨I, hIfin, hImem, hInhds⟩ := hfam y (hS hy)
  refine ⟨(fun W : B.atlas.saturatedAtlas.RecognizedSubset => W.locus) '' I,
    hIfin.image _, ?_, ?_⟩
  · rintro t ⟨W, hW, rfl⟩
    obtain ⟨hyW, P, hP⟩ := hImem W hW
    refine ⟨hyW, ?_⟩
    have hT2 : T2Space P.locus := inferInstance
    rw [hP] at hT2
    exact hT2
  · refine Filter.mem_of_superset hInhds ?_
    intro z hz
    obtain ⟨W, hW, hzW⟩ := Set.mem_iUnion₂.mp hz
    exact ⟨W.locus, ⟨W, hW, rfl⟩, hzW⟩

/-- Under exactly the family hypothesis of
`FiniteOverTargetLocalityStatement`, the literal preimage in `V` of every
Hausdorff subset of `U` (in particular of every recognized target affinoid
inside `U`) is Hausdorff. -/
theorem t2Space_inter_preimage_of_targetFamilies
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : Set A.space) (U : Set B.space)
    (hfam : ∀ x ∈ U, ∃ I : Set B.atlas.saturatedAtlas.RecognizedSubset,
      I.Finite ∧
      (∀ W ∈ I, x ∈ W.locus ∧ W.locus ⊆ U ∧
        ∃ (P : A.atlas.saturatedAtlas.RecognizedSubset)
          (h : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart),
          P.locus = V ∩ g.baseMap ⁻¹' W.locus ∧
            (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach) ∧
      (⋃ W ∈ I, W.locus) ∈ 𝓝 x)
    (S : Set B.space) [T2Space S] (hS : S ⊆ U) :
    T2Space ↥(V ∩ g.baseMap ⁻¹' S) := by
  refine g.t2Space_inter_preimage_of_recognizedFamilies V U ?_ S hS
  intro x hx
  obtain ⟨I, hIfin, hImem, hInhds⟩ := hfam x hx
  refine ⟨I, hIfin, fun W hW => ?_, hInhds⟩
  obtain ⟨hxW, -, P, -, hP, -⟩ := hImem W hW
  exact ⟨hxW, P, hP⟩

/-- The recognized-affinoid case used for chart recognition. -/
theorem t2Space_inter_preimage_locus_of_targetFamilies
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : Set A.space) (U : Set B.space)
    (hfam : ∀ x ∈ U, ∃ I : Set B.atlas.saturatedAtlas.RecognizedSubset,
      I.Finite ∧
      (∀ W ∈ I, x ∈ W.locus ∧ W.locus ⊆ U ∧
        ∃ (P : A.atlas.saturatedAtlas.RecognizedSubset)
          (h : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart),
          P.locus = V ∩ g.baseMap ⁻¹' W.locus ∧
            (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach) ∧
      (⋃ W ∈ I, W.locus) ∈ 𝓝 x)
    (W : B.atlas.saturatedAtlas.RecognizedSubset) (hW : W.locus ⊆ U) :
    T2Space ↥(V ∩ g.baseMap ⁻¹' W.locus) :=
  g.t2Space_inter_preimage_of_targetFamilies V U hfam W.locus hW

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
