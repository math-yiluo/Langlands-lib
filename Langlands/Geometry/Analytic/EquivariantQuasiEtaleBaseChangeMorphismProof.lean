import Langlands.Geometry.Analytic.CompatibleLocalizedFieldPoints
import Langlands.Geometry.Analytic.CompactProbeQuasiEtaleHausdorffComparisonProof
import Langlands.Geometry.Analytic.EquivariantQuasiEtaleBaseChangeMorphismStatement
import Langlands.Geometry.Analytic.EquivariantQuasiEtalePullbacksProof
import Langlands.Geometry.Analytic.QuasiEtaleFieldPointPullbacks

/-! # Equivariant quasi-étale base change is a morphism of sites -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.SpaceWithOperators

open _root_.CategoryTheory _root_.CategoryTheory.Limits Filter Set _root_.Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X : SpaceWithOperators.{u, v, v, z} K}

/-- Naturality of the analytic first projections is a pullback square. -/
theorem quasiEtalePullbackMap_isPullback (f : Y ⟶ X) {U V : EquivariantQuasiEtaleSite X.space}
    (g : U ⟶ V) :
    IsPullback (GSpace.forget.map ((quasiEtalePullbackFunctor f).map g).left)
      (GSpace.forget.map (quasiEtalePullbackProjection f U))
      (GSpace.forget.map (quasiEtalePullbackProjection f V))
      ((GSpace.forget (G := X.group.carrier)).map g.left) := by
  let F := quasiEtalePullbackFunctor f
  let H := GSpace.forget (K := K) (G := Y.group.carrier)
  let G := GSpace.forget (K := K) (G := X.group.carrier)
  have hp : H.map (F.map g).left ≫ H.map (quasiEtalePullbackProjection f V) =
      H.map (quasiEtalePullbackProjection f U) ≫ G.map g.left := by
    rw [← H.map_comp]
    change H.map ((F.map g).left ≫ quasiEtalePullbackProjection f V) =
      H.map (quasiEtalePullbackProjection f U) ≫ H.map ((GSpace.res f.groupHom).map g.left)
    rw [← H.map_comp]
    congr 1
    simp only [F, quasiEtalePullbackFunctor, Functor.comp_map, MorphismProperty.Over.pullback_map_left,
      quasiEtalePullbackProjection]
    have hV : HasPullback ((EquivariantQuasiEtaleSite.res f.groupHom).obj V).hom (restrictedHom f) :=
      MorphismProperty.hasPullback (P := GSpace.quasiEtale) _ ((EquivariantQuasiEtaleSite.res f.groupHom).obj V).prop
    exact @pullback.lift_fst _ _ _ _ _ _ _ _ hV _ _ _
  have h₁ : H.map (F.map g).left ≫ H.map (F.obj V).hom = H.map (F.obj U).hom := by
    rw [← H.map_comp, MorphismProperty.Over.w]
  have h₂ : G.map g.left ≫ G.map V.hom = G.map U.hom := by
    rw [← G.map_comp, MorphismProperty.Over.w]
  refine IsPullback.of_right ?_ hp (isPullback_quasiEtalePullbackFunctor f V).flip
  rw [h₁]
  change IsPullback (H.map (F.obj U).hom) (H.map (quasiEtalePullbackProjection f U)) f.hom
    (G.map g.left ≫ G.map V.hom)
  exact (congrArg (IsPullback (H.map (F.obj U).hom) (H.map (quasiEtalePullbackProjection f U)) f.hom)
    h₂).mpr (isPullback_quasiEtalePullbackFunctor f U).flip

private theorem exists_point_of_isPullback_of_quasiEtale
    {P A B C : LocalizedCategory.{u, v, v} (K := K)}
    {p : P ⟶ A} {q : P ⟶ B} {a : A ⟶ C} {b : B ⟶ C}
    (h : IsPullback p q a b) (ha : quasiEtale a)
    (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B)
    (hxy : localizedSpaceFunctor.map a x = localizedSpaceFunctor.map b y) :
    ∃ z : localizedSpaceFunctor.obj P,
      localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y := by
  obtain ⟨L, _, _, _, _, _, x', y', hx, hy, hxy'⟩ :=
    exists_compatible_localizedFieldPoints a b x y hxy
  obtain ⟨z, hz₁, hz₂⟩ := Types.exists_of_isPullback
    (localizedFieldPoint_isPullback_of_quasiEtale (L := L) h ha) x' y' hxy'
  refine ⟨((localizedFieldPointProjection L).app P z).down, ?_, ?_⟩
  · rw [← localizedFieldPointProjection_map_down, hz₁, hx]
  · rw [← localizedFieldPointProjection_map_down, hz₂, hy]

private theorem map_mem_quasiEtalePrecoverage (f : Y ⟶ X) {U : EquivariantQuasiEtaleSite X.space}
    {R : Presieve U} (hR : R ∈ equivariantQuasiEtalePrecoverage X.space U) :
    R.map (quasiEtalePullbackFunctor f) ∈ equivariantQuasiEtalePrecoverage Y.space
      ((quasiEtalePullbackFunctor f).obj U) := by
  classical
  let F := quasiEtalePullbackFunctor f
  let H := GSpace.forget (K := K) (G := Y.group.carrier)
  let G := GSpace.forget (K := K) (G := X.group.carrier)
  let b := H.map (quasiEtalePullbackProjection f U)
  rw [mem_equivariantQuasiEtalePrecoverage_iff] at hR ⊢
  change HasQuasiEtaleChartNeighborhoods _ at hR ⊢
  intro x
  change localizedSpaceFunctor.obj (H.obj (F.obj U).left) at x
  obtain ⟨σ, hσ, hn, hfamily⟩ := hR (localizedSpaceFunctor.map b x)
  let : WeaklyLocallyCompactSpace (localizedSpaceFunctor.obj (H.obj (F.obj U).left)) :=
    weaklyLocallyCompactSpace_localized _
  obtain ⟨N, hN, hnN⟩ := exists_compact_mem_nhds x
  have hpiece (W : Set (localizedSpaceFunctor.obj (G.obj U.left))) (hW : W ∈ σ) :
      ∃ δ : Set (Set (localizedSpaceFunctor.obj (H.obj (F.obj U).left))),
        δ.Finite ∧ N ∩ (localizedSpaceFunctor.map b ⁻¹' W) ⊆ ⋃₀ δ ∧
        ∀ T ∈ δ, ∃ (V : EquivariantQuasiEtaleSite Y.space) (g : V ⟶ F.obj U)
          (i : (presentationOf (H.obj V.left)).presentation.atlas.Index),
          R.map F g ∧ T = localizedSpaceFunctor.map (H.map g.left) ''
            ((presentationOf (H.obj V.left)).chartDomain i).carrier := by
    obtain ⟨_, a, i, ha, rfl⟩ := hfamily W hW
    cases ha with
    | of ha =>
      rename_i V g
      let a := G.map g.left
      let p : H.obj (F.obj V).left ⟶ G.obj V.left := H.map (quasiEtalePullbackProjection f V)
      let q := H.map (F.map g).left
      let C : Set (localizedSpaceFunctor.obj (G.obj V.left)) :=
        ((presentationOf (G.obj V.left)).chartDomain i).carrier
      have hC : IsCompact C := ((presentationOf (G.obj V.left)).isCompactDomain_chartDomain i).1
      have hP : IsPullback p q a b := (quasiEtalePullbackMap_isPullback f g).flip
      have hq := EquivariantQuasiEtaleSite.quasiEtale_map_left g
      let : T2Space (localizedSpaceFunctor.obj (G.obj U.left)) := U.left.2.1
      let : T2Space (localizedSpaceFunctor.obj (G.obj V.left)) := V.left.2.1
      let : T2Space (localizedSpaceFunctor.obj (H.obj (F.obj U).left)) := (F.obj U).left.2.1
      let Z : Set (localizedSpaceFunctor.obj (G.obj V.left) ×
          localizedSpaceFunctor.obj (H.obj (F.obj U).left)) :=
        (C ×ˢ N) ∩ {z | localizedSpaceFunctor.map a z.1 = localizedSpaceFunctor.map b z.2}
      have hZ : IsCompact Z :=
        (hC.prod hN).of_isClosed_subset (IsClosed.inter
          ((hC.prod hN).isClosed) (isClosed_eq
            ((localizedSpaceFunctor.map a).hom.continuous.comp continuous_fst)
            ((localizedSpaceFunctor.map b).hom.continuous.comp continuous_snd))) inter_subset_left
      have hL := (hasCompactPairPreimages_of_quasiEtale hP hq).2 Z hZ (fun _ hz => hz.2)
      let A := (presentationOf (H.obj (F.obj V).left)).presentation.atlas
      obtain ⟨ξ, hξ, hchart, hcov⟩ := A.isNet_chartFamily.1.exists_finite_cover_of_isCompact hL
      refine ⟨Set.image (localizedSpaceFunctor.map q) '' ξ, hξ.image _, ?_, ?_⟩
      · rintro y ⟨hy, z, hz, hzy⟩
        obtain ⟨t, ht₁, ht₂⟩ := exists_point_of_isPullback_of_quasiEtale hP hq z y hzy
        have ht : t ∈ localizedProjectionPair p q ⁻¹' Z := by
          change ((localizedSpaceFunctor.map p t, localizedSpaceFunctor.map q t) :
            localizedSpaceFunctor.obj (G.obj V.left) ×
              localizedSpaceFunctor.obj (H.obj (F.obj U).left)) ∈ Z
          rw [ht₁, ht₂]
          exact ⟨⟨hz, hy⟩, hzy⟩
        obtain ⟨T, hT, htT⟩ := mem_sUnion.mp (hcov ht)
        exact mem_sUnion.mpr ⟨_, ⟨T, hT, rfl⟩, t, htT, ht₂⟩
      · rintro _ ⟨T, hT, rfl⟩
        obtain ⟨j, rfl⟩ := hchart hT
        exact ⟨F.obj V, F.map g, j, Presieve.map_map ha, rfl⟩
  choose! δ hf hsub hδ using hpiece
  refine ⟨⋃ W ∈ σ, δ W, hσ.biUnion hf, ?_, ?_⟩
  · refine Filter.mem_of_superset (Filter.inter_mem hnN
      ((localizedSpaceFunctor.map b).hom.continuous.continuousAt.preimage_mem_nhds hn)) ?_
    rintro y ⟨hy, W, hW, hyW⟩
    obtain ⟨T, hT, hyT⟩ := mem_sUnion.mp (hsub W hW ⟨hy, hyW⟩)
    exact ⟨T, mem_iUnion₂.mpr ⟨W, hW, hT⟩, hyT⟩
  · intro T hT
    obtain ⟨W, hW, hWT⟩ := mem_iUnion₂.mp hT
    obtain ⟨V, g, i, hg, hTi⟩ := hδ W hW T hWT
    exact ⟨(EquivariantQuasiEtaleSite.toQuasiEtaleSite Y.space).obj V,
      (EquivariantQuasiEtaleSite.toQuasiEtaleSite Y.space).map g, i, Presieve.map_map hg, hTi⟩

/-- Fixed-field quasi-étale base change is a morphism of equivariant compact-probe sites. -/
theorem quasiEtalePullbackFunctor_morphismOfSites
    (f : Y ⟶ X) :
    RepresentablyFlat (quasiEtalePullbackFunctor f) ∧
      (quasiEtalePullbackFunctor f).IsContinuous (equivariantCompactProbeQuasiEtaleTopology X.space)
        (equivariantCompactProbeQuasiEtaleTopology Y.space) := by
  let F := quasiEtalePullbackFunctor f
  let H := GSpace.forget (K := K) (G := Y.group.carrier)
  refine GSpace.representablyFlat_and_isContinuous_of_isPullback_forget F
    (equivariantQuasiEtalePullbacks K X.group.carrier X.space) ?_ ?_
    (equivariantCompactProbeQuasiEtalePrecoverage X.space)
    (equivariantCompactProbeQuasiEtalePrecoverage Y.space) ?_
  · intro P U V W p q g h sq
    have hw := (GSpace.isPullback_of_isPullback_forget (P := GSpace.quasiEtale) sq).w
    have hcomp : H.map (F.map p).left ≫ H.map (F.map g).left =
        H.map (F.map q).left ≫ H.map (F.map h).left := by
      simp only [← H.map_comp, ← MorphismProperty.Comma.comp_left, ← F.map_comp, hw]
    refine IsPullback.of_bot ?_ hcomp (quasiEtalePullbackMap_isPullback f h)
    rw [(quasiEtalePullbackMap_isPullback f q).w, (quasiEtalePullbackMap_isPullback f g).w]
    exact (quasiEtalePullbackMap_isPullback f p).paste_vert sq
  · intro U hU
    let U' := (EquivariantQuasiEtaleSite.res f.groupHom).obj U
    have : IsIso U'.hom := (GSpace.res f.groupHom).map_isIso U.hom
    exact (IsPullback.of_hasPullback U'.hom (restrictedHom f)).isIso_snd_of_isIso
  · intro U R hR
    rw [equivariantCompactProbeQuasiEtalePrecoverage_eq_of_comparison
      (compactProbeQuasiEtaleHausdorffComparison K)] at hR ⊢
    exact map_mem_quasiEtalePrecoverage f hR

/-- The equivariant quasi-étale base-change morphism for all complete ground fields. -/
theorem equivariantQuasiEtaleBaseChangeMorphism :
    EquivariantQuasiEtaleBaseChangeMorphismStatement.{u, v, z} :=
  fun _ _ _ _ _ _ f => quasiEtalePullbackFunctor_morphismOfSites f

end Langlands.Analytic.SaturatedAtlasPresentation.SpaceWithOperators

