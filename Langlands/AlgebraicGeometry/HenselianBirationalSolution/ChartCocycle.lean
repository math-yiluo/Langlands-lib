import Langlands.AlgebraicGeometry.HenselianBirationalSolution.ChartData

/-! # The cocycle condition for the transition maps

For translations `τ₁`, `τ₂`, `τ₃`, the transition map of `(τ₁, τ₂)` maps the common overlap of
`(τ₁, τ₂)` and `(τ₁, τ₃)` into the overlap of `(τ₂, τ₃)`, and there the transition maps compose:
`ψ₂₃ ∘ ψ₁₂ = ψ₁₃`. Both statements hold on the dense open part where the transition maps are the
compositions `τⱼ⁻¹ ∘ τᵢ`; the first extends by closedness of the graph of `ψ₂₃`, the second because
the common overlap is reduced and `Y` is separated over `S`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}

namespace Translation

theorem dense_overlap (τ σ : Translation m) : Dense (overlap τ σ : Set Y) := by
  have h1 : Dense (τ.map ⁻¹' Set.range σ.map) :=
    (FibreGenerizationDense.dense σ.range_dense).preimage τ.map.isOpenMap
  have h2 : DenseRange τ.dom.ι := by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact dense_dom τ
  exact h2.dense_image τ.dom.ι.continuous h1

variable (τ₁ τ₂ τ₃ : Translation m)

/-- The dense open part of the common overlap where all transition maps are compositions of
translations. -/
def cocycleGeneric : Y.Opens :=
  (overlap τ₁ τ₂ ⊓ overlap τ₁ τ₃) ⊓ ((overlap τ₁ τ₂).ι ''ᵁ (trans τ₁ τ₂ ⁻¹ᵁ overlap τ₂ τ₃))

theorem dense_cocycleGeneric : Dense (cocycleGeneric τ₁ τ₂ τ₃ : Set Y) := by
  have h3 : Dense ((overlap τ₁ τ₂).ι '' (trans τ₁ τ₂ ⁻¹' overlap τ₂ τ₃)) := by
    have hd : DenseRange (overlap τ₁ τ₂).ι := by
      rw [DenseRange, Scheme.Opens.range_ι]
      exact dense_overlap τ₁ τ₂
    exact hd.dense_image (overlap τ₁ τ₂).ι.continuous
      ((dense_overlap τ₂ τ₃).preimage (trans τ₁ τ₂).isOpenMap)
  exact ((dense_overlap τ₁ τ₂).inter_of_isOpen_left (dense_overlap τ₁ τ₃)
    (overlap τ₁ τ₂).isOpen).inter_of_isOpen_left h3
    ((overlap τ₁ τ₂).isOpen.inter (overlap τ₁ τ₃).isOpen)

theorem cocycleGeneric_le₁₂ : cocycleGeneric τ₁ τ₂ τ₃ ≤ overlap τ₁ τ₂ :=
  fun _ hx => hx.1.1

theorem cocycleGeneric_le₁₃ : cocycleGeneric τ₁ τ₂ τ₃ ≤ overlap τ₁ τ₃ :=
  fun _ hx => hx.1.2

theorem range_cocycleGeneric_trans :
    Set.range (Y.homOfLE (cocycleGeneric_le₁₂ τ₁ τ₂ τ₃) ≫ trans τ₁ τ₂) ⊆
      Set.range (overlap τ₂ τ₃).ι := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨z, hz, hzx⟩ := x.2.2
  have hx : Y.homOfLE (cocycleGeneric_le₁₂ τ₁ τ₂ τ₃) x = z := by
    apply (overlap τ₁ τ₂).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact hzx.symm
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, hx]
  exact hz

/-- `σ₂⁻¹ ∘ σ₁` on the generic part, landing in the overlap of `(τ₂, τ₃)`. -/
def cocycleE : (cocycleGeneric τ₁ τ₂ τ₃).toScheme ⟶ (overlap τ₂ τ₃).toScheme :=
  IsOpenImmersion.lift (overlap τ₂ τ₃).ι _ (range_cocycleGeneric_trans τ₁ τ₂ τ₃)

@[reassoc (attr := simp)]
theorem cocycleE_ι : cocycleE τ₁ τ₂ τ₃ ≫ (overlap τ₂ τ₃).ι =
    Y.homOfLE (cocycleGeneric_le₁₂ τ₁ τ₂ τ₃) ≫ trans τ₁ τ₂ :=
  IsOpenImmersion.lift_fac _ _ _

/-- On the generic part, `τ₃⁻¹ ∘ τ₂ ∘ τ₂⁻¹ ∘ τ₁ = τ₃⁻¹ ∘ τ₁`. -/
theorem cocycleE_trans : cocycleE τ₁ τ₂ τ₃ ≫ trans τ₂ τ₃ =
    Y.homOfLE (cocycleGeneric_le₁₃ τ₁ τ₂ τ₃) ≫ trans τ₁ τ₃ := by
  have h1 : cocycleE τ₁ τ₂ τ₃ ≫ overlapIncl τ₂ τ₃ =
      Y.homOfLE (cocycleGeneric_le₁₂ τ₁ τ₂ τ₃) ≫ transLift τ₁ τ₂ := by
    rw [← cancel_mono τ₂.dom.ι, Category.assoc, Scheme.homOfLE_ι, cocycleE_ι, Category.assoc]
    rfl
  have h2 : cocycleE τ₁ τ₂ τ₃ ≫ transLift τ₂ τ₃ =
      Y.homOfLE (cocycleGeneric_le₁₃ τ₁ τ₂ τ₃) ≫ transLift τ₁ τ₃ := by
    rw [← cancel_mono τ₃.map, Category.assoc, trans_map, reassoc_of% h1, trans_map,
      Category.assoc, trans_map, ← Category.assoc, ← Category.assoc, Scheme.homOfLE_homOfLE,
      Scheme.homOfLE_homOfLE]
  change cocycleE τ₁ τ₂ τ₃ ≫ transLift τ₂ τ₃ ≫ τ₃.dom.ι = _ ≫ transLift τ₁ τ₃ ≫ τ₃.dom.ι
  rw [reassoc_of% h2]

section Hyp

variable [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m)

/-- The common overlap of `(τ₁, τ₂)` and `(τ₁, τ₃)`. -/
abbrev commonOverlap : Y.Opens := chartOverlap τ₁ τ₂ H ⊓ chartOverlap τ₁ τ₃ H

theorem cocycleGeneric_le : cocycleGeneric τ₁ τ₂ τ₃ ≤ commonOverlap τ₁ τ₂ τ₃ H :=
  fun _ hx => ⟨overlap_le_chartOverlap τ₁ τ₂ H hx.1.1, overlap_le_chartOverlap τ₁ τ₃ H hx.1.2⟩

/-- `ψ₁₂` on the common overlap. -/
abbrev cocA : (commonOverlap τ₁ τ₂ τ₃ H).toScheme ⟶ Y :=
  Y.homOfLE inf_le_left ≫ chartTrans τ₁ τ₂ H

/-- `ψ₁₃` on the common overlap. -/
abbrev cocB : (commonOverlap τ₁ τ₂ τ₃ H).toScheme ⟶ Y :=
  Y.homOfLE inf_le_right ≫ chartTrans τ₁ τ₃ H

theorem cocA_g : cocA τ₁ τ₂ τ₃ H ≫ g = cocB τ₁ τ₂ τ₃ H ≫ g := by
  rw [Category.assoc, Category.assoc, chartTrans_comp_g, chartTrans_comp_g,
    Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]

theorem homOfLE_cocA : Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H) ≫ cocA τ₁ τ₂ τ₃ H =
    cocycleE τ₁ τ₂ τ₃ ≫ (overlap τ₂ τ₃).ι := by
  rw [cocA, ← Category.assoc, Scheme.homOfLE_homOfLE,
    ← Scheme.homOfLE_homOfLE Y (cocycleGeneric_le₁₂ τ₁ τ₂ τ₃) (overlap_le_chartOverlap τ₁ τ₂ H),
    Category.assoc, homOfLE_chartTrans, cocycleE_ι]

theorem homOfLE_cocB : Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H) ≫ cocB τ₁ τ₂ τ₃ H =
    cocycleE τ₁ τ₂ τ₃ ≫ trans τ₂ τ₃ := by
  rw [cocB, ← Category.assoc, Scheme.homOfLE_homOfLE,
    ← Scheme.homOfLE_homOfLE Y (cocycleGeneric_le₁₃ τ₁ τ₂ τ₃) (overlap_le_chartOverlap τ₁ τ₃ H),
    Category.assoc, homOfLE_chartTrans, cocycleE_trans]

theorem denseRange_homOfLE_generic :
    DenseRange (Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H)) := by
  apply denseRange_of_comp_isOpenEmbedding (commonOverlap τ₁ τ₂ τ₃ H).ι.isOpenEmbedding
  have hfun : ⇑(commonOverlap τ₁ τ₂ τ₃ H).ι ∘ ⇑(Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H)) =
      ⇑(cocycleGeneric τ₁ τ₂ τ₃).ι := by
    ext t
    simp only [Function.comp_apply]
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  rw [hfun, DenseRange, Scheme.Opens.range_ι]
  exact dense_cocycleGeneric τ₁ τ₂ τ₃

/-- `ψ₁₂` maps the common overlap into the overlap of `(τ₂, τ₃)`. -/
theorem cocA_mem (w : (commonOverlap τ₁ τ₂ τ₃ H).toScheme) :
    cocA τ₁ τ₂ τ₃ H w ∈ chartOverlap τ₂ τ₃ H := by
  set P := pullback.lift (cocA τ₁ τ₂ τ₃ H) (cocB τ₁ τ₂ τ₃ H) (cocA_g τ₁ τ₂ τ₃ H)
  have hP : Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H) ≫ P = cocycleE τ₁ τ₂ τ₃ ≫ graph τ₂ τ₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, homOfLE_cocA, Category.assoc, graph_fst]
    · rw [Category.assoc, pullback.lift_snd, homOfLE_cocB, Category.assoc, graph_snd]
  have hC : IsClosed (P ⁻¹' Set.range (graph τ₂ τ₃).imageι) :=
    (isClosed_range_imageι τ₂ τ₃).preimage P.continuous
  have hsub : Set.range (Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H)) ⊆
      P ⁻¹' Set.range (graph τ₂ τ₃).imageι := by
    rintro _ ⟨t, rfl⟩
    show P (Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H) t) ∈ Set.range (graph τ₂ τ₃).imageι
    rw [← Scheme.Hom.comp_apply, hP, Scheme.Hom.comp_apply, range_imageι]
    exact subset_closure ⟨_, rfl⟩
  have hall : P w ∈ Set.range (graph τ₂ τ₃).imageι := by
    have h := hC.closure_subset_iff.mpr hsub
    rw [(denseRange_homOfLE_generic τ₁ τ₂ τ₃ H).closure_range] at h
    exact h (Set.mem_univ w)
  obtain ⟨γ, hγ⟩ := hall
  refine ⟨γ, ?_⟩
  show (pr₁ τ₂ τ₃) γ = cocA τ₁ τ₂ τ₃ H w
  rw [pr₁, Scheme.Hom.comp_apply, hγ, ← Scheme.Hom.comp_apply, pullback.lift_fst]

theorem range_cocA : Set.range (cocA τ₁ τ₂ τ₃ H) ⊆ Set.range (chartOverlap τ₂ τ₃ H).ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact cocA_mem τ₁ τ₂ τ₃ H w

/-- `ψ₁₂` on the common overlap, as a map into the overlap of `(τ₂, τ₃)`. -/
def cocA' : (commonOverlap τ₁ τ₂ τ₃ H).toScheme ⟶ (chartOverlap τ₂ τ₃ H).toScheme :=
  IsOpenImmersion.lift _ _ (range_cocA τ₁ τ₂ τ₃ H)

@[reassoc (attr := simp)]
theorem cocA'_ι : cocA' τ₁ τ₂ τ₃ H ≫ (chartOverlap τ₂ τ₃ H).ι = cocA τ₁ τ₂ τ₃ H :=
  IsOpenImmersion.lift_fac _ _ _

/-- **Cocycle condition.** `ψ₂₃ ∘ ψ₁₂ = ψ₁₃` on the common overlap. -/
theorem cocA'_chartTrans : cocA' τ₁ τ₂ τ₃ H ≫ chartTrans τ₂ τ₃ H = cocB τ₁ τ₂ τ₃ H := by
  have : IsDominant (Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H)) :=
    ⟨denseRange_homOfLE_generic τ₁ τ₂ τ₃ H⟩
  refine ext_of_isDominant_of_isSeparated g ?_ (Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H)) ?_
  · rw [Category.assoc, chartTrans_comp_g, cocA'_ι_assoc, ← Category.assoc]
    exact cocA_g τ₁ τ₂ τ₃ H
  · have h1 : Y.homOfLE (cocycleGeneric_le τ₁ τ₂ τ₃ H) ≫ cocA' τ₁ τ₂ τ₃ H =
        cocycleE τ₁ τ₂ τ₃ ≫ Y.homOfLE (overlap_le_chartOverlap τ₂ τ₃ H) := by
      rw [← cancel_mono (chartOverlap τ₂ τ₃ H).ι, Category.assoc, cocA'_ι, homOfLE_cocA,
        Category.assoc, Scheme.homOfLE_ι]
    rw [reassoc_of% h1, homOfLE_chartTrans, homOfLE_cocB]

/-- The cocycle condition on points: if `x` lies in the overlaps of `(τ₁, τ₂)` and `(τ₁, τ₃)`
then `ψ₁₂ x` lies in the overlap of `(τ₂, τ₃)` and `ψ₂₃ (ψ₁₂ x) = ψ₁₃ x`. -/
theorem chartCocycle {T : Scheme.{u}} (x₁ : T ⟶ (chartOverlap τ₁ τ₂ H).toScheme)
    (x₂ : T ⟶ (chartOverlap τ₁ τ₃ H).toScheme)
    (h : x₁ ≫ (chartOverlap τ₁ τ₂ H).ι = x₂ ≫ (chartOverlap τ₁ τ₃ H).ι) :
    ∃ y : T ⟶ (chartOverlap τ₂ τ₃ H).toScheme,
      y ≫ (chartOverlap τ₂ τ₃ H).ι = x₁ ≫ chartTrans τ₁ τ₂ H ∧
        y ≫ chartTrans τ₂ τ₃ H = x₂ ≫ chartTrans τ₁ τ₃ H := by
  have hr : Set.range (x₁ ≫ (chartOverlap τ₁ τ₂ H).ι) ⊆
      Set.range (commonOverlap τ₁ τ₂ τ₃ H).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.comp_apply]
      exact (x₁ t).2
    · rw [h, Scheme.Hom.comp_apply]
      exact (x₂ t).2
  set w := IsOpenImmersion.lift (commonOverlap τ₁ τ₂ τ₃ H).ι _ hr
  have hw : w ≫ (commonOverlap τ₁ τ₂ τ₃ H).ι = x₁ ≫ (chartOverlap τ₁ τ₂ H).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have hw1 : w ≫ Y.homOfLE inf_le_left = x₁ := by
    rw [← cancel_mono (chartOverlap τ₁ τ₂ H).ι, Category.assoc, Scheme.homOfLE_ι, hw]
  have hw2 : w ≫ Y.homOfLE inf_le_right = x₂ := by
    rw [← cancel_mono (chartOverlap τ₁ τ₃ H).ι, Category.assoc, Scheme.homOfLE_ι, hw, h]
  refine ⟨w ≫ cocA' τ₁ τ₂ τ₃ H, ?_, ?_⟩
  · rw [Category.assoc, cocA'_ι, cocA, ← Category.assoc, hw1]
  · rw [Category.assoc, cocA'_chartTrans, cocB, ← Category.assoc, hw2]

end Hyp

end Translation

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
