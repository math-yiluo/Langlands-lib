import Langlands.AlgebraicGeometry.HenselianBirationalSolution.GraphInjective

/-! # Overlaps and transition maps of the charts

For translations `τ`, `σ`, the first projection of the closure `Γ` of the graph of `σ⁻¹ ∘ τ`
identifies `Γ` with an open `chartOverlap τ σ` of `Y`, and the second projection becomes an open
immersion `chartTrans τ σ : chartOverlap τ σ ⟶ Y` extending `σ⁻¹ ∘ τ`. Its graph is closed, its
image is `chartOverlap σ τ`, and for `σ = τ` it is the identity of `Y`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}

/-- The hypotheses under which the projections of the closures of graphs are open immersions:
`m` is strict on its domain and `Y` is normal. -/
structure GlueHyp (m : BirationalGroupLaw g) : Prop where
  strict : IsStrictDomain m
  normal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)

namespace Translation

variable (τ σ : Translation m)

theorem range_imageι [IsNoetherian Y] :
    Set.range (graph τ σ).imageι = closure (Set.range (graph τ σ)) := by
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

theorem isClosed_range_imageι : IsClosed (Set.range (graph τ σ).imageι) :=
  (graph τ σ).imageι.isClosedEmbedding.isClosed_range

variable [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m)

/-- The open of `Y` on which `σ⁻¹ ∘ τ` extends: the image of the first projection of `Γ`. -/
def chartOverlap : Y.Opens :=
  ⟨Set.range (pr₁ τ σ), by
    have := isOpenImmersion_pr₁ τ σ H.strict H.normal
    exact (pr₁ τ σ).isOpenEmbedding.isOpen_range⟩

/-- `Γ` is isomorphic to `chartOverlap τ σ` through the first projection. -/
def chartIso : graphImage τ σ ≅ (chartOverlap τ σ H).toScheme :=
  have := isOpenImmersion_pr₁ τ σ H.strict H.normal
  IsOpenImmersion.isoOfRangeEq (pr₁ τ σ) (chartOverlap τ σ H).ι
    (Scheme.Opens.range_ι (chartOverlap τ σ H)).symm

@[reassoc (attr := simp)]
theorem chartIso_hom_ι : (chartIso τ σ H).hom ≫ (chartOverlap τ σ H).ι = pr₁ τ σ := by
  have := isOpenImmersion_pr₁ τ σ H.strict H.normal
  exact IsOpenImmersion.isoOfRangeEq_hom_fac (pr₁ τ σ) (chartOverlap τ σ H).ι
    (Scheme.Opens.range_ι (chartOverlap τ σ H)).symm

@[reassoc (attr := simp)]
theorem chartIso_inv_pr₁ : (chartIso τ σ H).inv ≫ pr₁ τ σ = (chartOverlap τ σ H).ι := by
  rw [← chartIso_hom_ι, Iso.inv_hom_id_assoc]

/-- The transition map: the extension of `σ⁻¹ ∘ τ` to `chartOverlap τ σ`. -/
def chartTrans : (chartOverlap τ σ H).toScheme ⟶ Y := (chartIso τ σ H).inv ≫ pr₂ τ σ

instance : IsOpenImmersion (chartTrans τ σ H) := by
  have := isOpenImmersion_pr₂ τ σ H.strict H.normal
  rw [chartTrans]
  infer_instance

theorem chartTrans_comp_g : chartTrans τ σ H ≫ g = (chartOverlap τ σ H).ι ≫ g := by
  rw [chartTrans, Category.assoc, ← pr₁_comp_g, ← Category.assoc, chartIso_inv_pr₁]

theorem range_chartTrans : Set.range (chartTrans τ σ H) = Set.range (pr₂ τ σ) := by
  have hsurj : Function.Surjective (chartIso τ σ H).inv :=
    (Scheme.homeoOfIso (chartIso τ σ H).symm).surjective
  rw [chartTrans, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
    Set.image_univ]

theorem overlap_le_chartOverlap : overlap τ σ ≤ chartOverlap τ σ H := by
  intro x hx
  refine ⟨(graph τ σ).toImage (show (overlap τ σ).toScheme from ⟨x, hx⟩), ?_⟩
  rw [← Scheme.Hom.comp_apply, toImage_pr₁]
  rfl

theorem toImage_chartIso :
    (graph τ σ).toImage ≫ (chartIso τ σ H).hom = Y.homOfLE (overlap_le_chartOverlap τ σ H) := by
  rw [← cancel_mono (chartOverlap τ σ H).ι, Category.assoc, chartIso_hom_ι, toImage_pr₁,
    Scheme.homOfLE_ι]

/-- On the overlap, the transition map is `σ⁻¹ ∘ τ`. -/
@[reassoc]
theorem homOfLE_chartTrans :
    Y.homOfLE (overlap_le_chartOverlap τ σ H) ≫ chartTrans τ σ H = trans τ σ := by
  rw [← toImage_chartIso, chartTrans, Category.assoc, Iso.hom_inv_id_assoc, toImage_pr₂]

/-- The graph of the transition map is the closure of the graph of `σ⁻¹ ∘ τ`. -/
theorem graph_chartTrans :
    pullback.lift (chartOverlap τ σ H).ι (chartTrans τ σ H) (chartTrans_comp_g τ σ H).symm =
      (chartIso τ σ H).inv ≫ (graph τ σ).imageι := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, ← chartIso_inv_pr₁]
  · rw [pullback.lift_snd, Category.assoc]
    rfl

/-- The image of the transition map of `(τ, σ)` is the overlap of `(σ, τ)`. -/
theorem range_chartTrans_eq :
    Set.range (chartTrans τ σ H) = (chartOverlap σ τ H : Set Y) := by
  rw [range_chartTrans]
  change Set.range (pr₂ τ σ) = Set.range (pr₁ σ τ)
  set s := Scheme.homeoOfIso (pullbackSymmetry g g)
  have hs : ∀ p, s p = (pullbackSymmetry g g).hom p := fun _ => rfl
  have himg : s '' Set.range (graph τ σ) = Set.range (graph σ τ) := by
    apply le_antisymm
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact image_swap_range_graph τ σ ⟨q, hq, (hs q).symm⟩
    · intro p hp
      have h2 := image_swap_range_graph σ τ ⟨p, hp, rfl⟩
      refine ⟨(pullbackSymmetry g g).hom p, h2, ?_⟩
      have hss : (pullbackSymmetry g g).hom ≫ (pullbackSymmetry g g).hom = 𝟙 _ := by
        apply pullback.hom_ext <;> simp
      rw [hs, ← Scheme.Hom.comp_apply, hss]
      rfl
  have hcl : s '' Set.range (graph τ σ).imageι = Set.range (graph σ τ).imageι := by
    rw [range_imageι, range_imageι, ← himg, s.image_closure]
  simp only [pr₂, pr₁, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hcl,
    Set.image_image]
  congr 1
  ext p
  rw [hs, ← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]

omit [Smooth g] [Surjective g] [QuasiCompact g] in
theorem pr₁_eq_pr₂_self : pr₁ τ τ = pr₂ τ τ := by
  have : IsReduced (graphImage τ τ) := isReduced_image _
  exact ext_of_isDominant_of_isSeparated g (pr₁_comp_g τ τ) (graph τ τ).toImage
    (by rw [toImage_pr₁, toImage_pr₂, trans_self])

theorem chartOverlap_self : chartOverlap τ τ H = ⊤ := by
  have hdiag : (graph τ τ).imageι = pr₁ τ τ ≫ pullback.diagonal g := by
    apply pullback.hom_ext
    · simp
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, pr₁_eq_pr₂_self]
  have hclosed : IsClosed (Set.range (pr₁ τ τ)) := by
    have hpre : Set.range (pr₁ τ τ) = pullback.diagonal g ⁻¹' Set.range (graph τ τ).imageι := by
      ext y
      constructor
      · rintro ⟨γ, rfl⟩
        refine ⟨γ, ?_⟩
        rw [hdiag, Scheme.Hom.comp_apply]
      · rintro ⟨γ, hγ⟩
        refine ⟨γ, ?_⟩
        have := congrArg (pullback.fst g g) hγ
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.diagonal_fst] at this
        exact this
    rw [hpre]
    exact (isClosed_range_imageι τ τ).preimage (pullback.diagonal g).continuous
  have hsub : (τ.dom : Set Y) ⊆ Set.range (pr₁ τ τ) := by
    rw [← overlap_self]
    exact overlap_le_chartOverlap τ τ H
  rw [eq_top_iff]
  intro y _
  have := (hclosed.closure_subset_iff.mpr hsub) ((dense_dom τ).closure_eq ▸ Set.mem_univ y)
  exact this

theorem chartTrans_self : chartTrans τ τ H = (chartOverlap τ τ H).ι := by
  rw [chartTrans, ← pr₁_eq_pr₂_self, chartIso_inv_pr₁]

end Translation

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
