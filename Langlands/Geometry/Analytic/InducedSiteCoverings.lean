import Langlands.Geometry.Analytic.InducedEquivariantSite
import Langlands.Geometry.Analytic.InducedSpacePoints

/-! # Induction on equivariant quasi-étale sites preserves and reflects coverings -/

noncomputable section

universe u v z

open CategoryTheory Topology

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The covering condition of a quasi-étale site for the image of a presieve under a functor
into that site: the chart images are taken over the arrows of the original presieve. -/
theorem map_mem_quasiEtalePrecoverage_iff {C : Type*} [Category C]
    {Y : LocalizedCategory.{u, v, v} (K := K)} (F : C ⥤ QuasiEtaleSite Y) {U : C}
    (R : Presieve U) :
    R.map F ∈ quasiEtalePrecoverage Y (F.obj U) ↔
      ∀ x : localizedSpaceFunctor.obj (F.obj U).left,
        ∃ σ : Set (Set (localizedSpaceFunctor.obj (F.obj U).left)), σ.Finite ∧ ⋃₀ σ ∈ 𝓝 x ∧
          ∀ T ∈ σ, ∃ (V : C) (g : V ⟶ U)
            (i : (localizedObjectEquiv.symm (F.obj V).left).presentation.atlas.Index), R g ∧
            T = localizedSpaceFunctor.map (F.map g).left ''
              Set.range ((localizedObjectEquiv.symm (F.obj V).left).presentation.atlas.chart i) := by
  rw [mem_quasiEtalePrecoverage_iff]
  refine forall_congr' fun x => exists_congr fun σ => and_congr_right fun _ =>
    and_congr_right fun _ => forall₂_congr fun T _ => ?_
  constructor
  · rintro ⟨V, f, i, ⟨hg⟩, rfl⟩
    exact ⟨_, _, i, hg, rfl⟩
  · rintro ⟨V, g, i, hg, rfl⟩
    exact ⟨F.obj V, F.map g, i, Presieve.map_map hg, rfl⟩

namespace InducedSpace

/-! ## Finite covers of a disjoint union of copies -/

/-- Let `C` be a family of subsets of `Y` and `C'` a family of subsets of the disjoint union
`Σ c : ι, Y` of copies of `Y`, such that the copy of every nonempty member of `C` in every
summand belongs to `C'`, and every member of `C'` is the copy of a member of `C` in some
summand. Then every point of the disjoint union has a neighbourhood that is a finite union of
members of `C'` exactly when every point of `Y` has a neighbourhood that is a finite union of
members of `C`. -/
theorem sigma_finite_union_nhds_iff {ι : Type*} [Nonempty ι] {Y : Type*} [TopologicalSpace Y]
    (C : Set (Set Y)) (C' : Set (Set ((_ : ι) × Y)))
    (hC : ∀ T ∈ C, T.Nonempty → ∀ c : ι, Sigma.mk c '' T ∈ C')
    (hC' : ∀ T' ∈ C', ∃ (c : ι) (T : Set Y), T ∈ C ∧ T' = Sigma.mk c '' T) :
    (∀ z : (_ : ι) × Y, ∃ σ' : Set (Set ((_ : ι) × Y)), σ'.Finite ∧ ⋃₀ σ' ∈ 𝓝 z ∧
        ∀ T' ∈ σ', T' ∈ C') ↔
      ∀ y : Y, ∃ σ : Set (Set Y), σ.Finite ∧ ⋃₀ σ ∈ 𝓝 y ∧ ∀ T ∈ σ, T ∈ C := by
  constructor
  · intro h y
    obtain ⟨c₀⟩ := ‹Nonempty ι›
    obtain ⟨σ', hfin, hnhds, hsub⟩ := h ⟨c₀, y⟩
    refine ⟨{T | T ∈ C ∧ Sigma.mk c₀ '' T ∈ σ'}, ?_, ?_, fun T hT => hT.1⟩
    · exact (hfin.preimage (Set.image_injective.mpr sigma_mk_injective).injOn).subset
        fun T hT => hT.2
    · refine Filter.mem_of_superset
        ((continuous_sigmaMk (σ := fun _ : ι => Y) (i := c₀)).continuousAt.preimage_mem_nhds
          hnhds) ?_
      rintro w ⟨T', hT', hw⟩
      obtain ⟨c, T, hT, rfl⟩ := hC' T' (hsub T' hT')
      obtain ⟨t, ht, hteq⟩ := hw
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp hteq
      obtain rfl := eq_of_heq h2
      exact ⟨T, ⟨hT, hT'⟩, ht⟩
  · rintro h ⟨c, y⟩
    obtain ⟨σ, hfin, hnhds, hsub⟩ := h y
    refine ⟨Set.image (Sigma.mk c) '' {T | T ∈ σ ∧ T.Nonempty},
      (hfin.subset fun T hT => hT.1).image _, ?_, ?_⟩
    · have himg : Sigma.mk c '' ⋃₀ σ ∈ 𝓝 (⟨c, y⟩ : (_ : ι) × Y) :=
        isOpenMap_sigmaMk.image_mem_nhds hnhds
      refine Filter.mem_of_superset himg ?_
      rintro _ ⟨w, ⟨T, hT, hw⟩, rfl⟩
      exact ⟨Sigma.mk c '' T, ⟨T, ⟨hT, w, hw⟩, rfl⟩, w, hw, rfl⟩
    · rintro _ ⟨T, ⟨hT, hne⟩, rfl⟩
      exact hC T (hsub T hT) hne c

/-! ## Charts of induced spaces -/

section Charts

variable {G : Type z} [Group G] (H : Subgroup G)

/-- Every chart of an induced space is the copy of a chart of the original space in one
summand. -/
theorem exists_range_chart_inducedAction
    (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H)
    (k : (localizedObjectEquiv.symm (inducedAction H X).V).presentation.atlas.Index) :
    ∃ (c : G ⧸ H) (i : (localizedObjectEquiv.symm X.V).presentation.atlas.Index),
      Set.range ((localizedObjectEquiv.symm (inducedAction H X).V).presentation.atlas.chart k) =
        Sigma.mk c '' Set.range ((localizedObjectEquiv.symm X.V).presentation.atlas.chart i) := by
  obtain ⟨⟨⟨c, j⟩, dom⟩, hD⟩ := k.2
  obtain ⟨i, hi⟩ := (localizedObjectEquiv.symm X.V).hasAllLocalDomains.exists_chart
    (⟨j.1, dom⟩ :
      IndexedAffinoidAtlas.LocalDomain (localizedObjectEquiv.symm X.V).presentation.atlas)
  refine ⟨c, i, (IndexedAffinoidAtlas.range_saturatedChart _ _).trans (hD.symm.trans ?_)⟩
  have e : Sigma.mk (β := fun _ : G ⧸ H => (localizedObjectEquiv.symm X.V).presentation.space) c ''
      (⟨j.1, dom⟩ :
        IndexedAffinoidAtlas.LocalDomain (localizedObjectEquiv.symm X.V).presentation.atlas).locus =
      Sigma.mk c '' Set.range ((localizedObjectEquiv.symm X.V).presentation.atlas.chart i) := by
    rw [hi]
  exact (Set.image_comp
    (Sigma.mk (β := fun _ : G ⧸ H => (localizedObjectEquiv.symm X.V).presentation.space) c)
    ((localizedObjectEquiv.symm X.V).presentation.atlas.chart j.1) dom.locus).trans e

/-- The copy of a nonempty chart of the original space in any summand is a chart of the
induced space. -/
theorem exists_range_chart_inducedAction_eq
    (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H) (c : G ⧸ H)
    (i : (localizedObjectEquiv.symm X.V).presentation.atlas.Index)
    (hi : (Set.range ((localizedObjectEquiv.symm X.V).presentation.atlas.chart i)).Nonempty) :
    ∃ k : (localizedObjectEquiv.symm (inducedAction H X).V).presentation.atlas.Index,
      Set.range ((localizedObjectEquiv.symm (inducedAction H X).V).presentation.atlas.chart k) =
        Sigma.mk c '' Set.range ((localizedObjectEquiv.symm X.V).presentation.atlas.chart i) := by
  obtain ⟨_, y, rfl⟩ := hi
  let S : G ⧸ H → SaturatedAtlasPresentation.{u, max z v, max z v} K :=
    fun _ => localizedObjectEquiv.symm X.V
  let D : IndexedAffinoidAtlas.LocalDomain
      (AtlasDisjointUnion.atlas (fun j => (nonemptyFamily S j).atlas)
        (nonemptyFamily_hasNonemptyCharts S)) :=
    ⟨⟨c, ⟨i, ⟨y⟩⟩⟩, PresentedAffinoidAlgebra.Domain.whole K _⟩
  refine ⟨⟨D.locus, D, rfl⟩, ?_⟩
  rw [show Set.range ((localizedObjectEquiv.symm (inducedAction H X).V).presentation.atlas.chart
      ⟨D.locus, D, rfl⟩) = D.locus from IndexedAffinoidAtlas.range_saturatedChart _ _]
  change AtlasDisjointUnion.chart _ _ '' Set.univ = _
  rw [Set.image_univ, AtlasDisjointUnion.range_chart]
  rfl

end Charts

/-! ## Coverings -/

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  (hH : IsOpen (H : Set G)) (hC : ContinuityStatement.{u, v, z})
  (hQ : MorphismPropertyStatement.{u, v, z}) (X : GSpace.{u, max z v, max z v} K H)

/-- The induced `G`-morphism acts on points copywise. -/
theorem localizedSpaceFunctor_map_forget_map_gSpaceInduction_map_apply
    {W W' : GSpace.{u, max z v, max z v} K H} (φ : W ⟶ W') (c : G ⧸ H)
    (x : localizedSpaceFunctor.obj (GSpace.forget.obj W)) :
    localizedSpaceFunctor.map (GSpace.forget.map ((gSpaceInduction hH hC).map φ))
        (⟨c, x⟩ : (_ : G ⧸ H) × (localizedObjectEquiv.symm (GSpace.forget.obj W)).presentation.space) =
      (⟨c, localizedSpaceFunctor.map (GSpace.forget.map φ) x⟩ :
        (_ : G ⧸ H) × (localizedObjectEquiv.symm (GSpace.forget.obj W')).presentation.space) :=
  inductionFunctor_map_space_apply H ((ObjectProperty.ι _).map φ) c x

/-- **Induction preserves and reflects coverings** (Berkovich 1996, Example 1.2.1(i)): a family
`{U_i(H) → U(H)}` is a covering of `Qét(X(H))` exactly when the induced family
`{U_{i,G/H}(G) → U_{G/H}(G)}` is a covering of `Qét(X_{G/H}(G))`. -/
theorem map_quasiEtaleSiteInduction_mem_iff (U : EquivariantQuasiEtaleSite X) (R : Presieve U) :
    R.map (quasiEtaleSiteInduction hH hC hQ X) ∈
        equivariantQuasiEtalePrecoverage _ ((quasiEtaleSiteInduction hH hC hQ X).obj U) ↔
      R ∈ equivariantQuasiEtalePrecoverage X U := by
  have h : (equivariantQuasiEtalePrecoverage ((gSpaceInduction hH hC).obj X)).comap
      (quasiEtaleSiteInduction hH hC hQ X) =
        (quasiEtalePrecoverage (GSpace.forget.obj ((gSpaceInduction hH hC).obj X))).comap
          (quasiEtaleSiteInduction hH hC hQ X ⋙
            EquivariantQuasiEtaleSite.toQuasiEtaleSite ((gSpaceInduction hH hC).obj X)) := by
    rw [equivariantQuasiEtalePrecoverage, Precoverage.comap_comp]
  rw [← Precoverage.mem_comap_iff (F := quasiEtaleSiteInduction hH hC hQ X), h,
    Precoverage.mem_comap_iff, mem_equivariantQuasiEtalePrecoverage_iff,
    map_mem_quasiEtalePrecoverage_iff, map_mem_quasiEtalePrecoverage_iff]
  have : Nonempty (G ⧸ H) := ⟨baseCoset H⟩
  refine sigma_finite_union_nhds_iff (ι := G ⧸ H)
    (Y := localizedSpaceFunctor.obj (GSpace.forget.obj U.left)) _ _ ?_ ?_
  · rintro _ ⟨V, g, i, hg, rfl⟩ hne c
    obtain ⟨k, hk⟩ := exists_range_chart_inducedAction_eq H V.left.obj c i hne.of_image
    refine ⟨V, g, k, hg, ?_⟩
    erw [hk, Set.image_image, Set.image_image]
    exact Set.image_congr fun x _ =>
      (localizedSpaceFunctor_map_forget_map_gSpaceInduction_map_apply hH hC g.left c x).symm
  · rintro _ ⟨V, g, k, hg, rfl⟩
    obtain ⟨c, i, hk⟩ := exists_range_chart_inducedAction H V.left.obj k
    refine ⟨c, _, ⟨V, g, i, hg, rfl⟩, ?_⟩
    erw [hk, Set.image_image, Set.image_image]
    exact Set.image_congr fun x _ =>
      localizedSpaceFunctor_map_forget_map_gSpaceInduction_map_apply hH hC g.left c x

end InducedSpace

end Langlands.Analytic.SaturatedAtlasPresentation
