import Langlands.Geometry.Analytic.LocalizedDisjointUnion
import Langlands.Geometry.Analytic.LocalizedPullbackDescent
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.RigidityTransport

/-! # Test relations on disjoint unions of analytic spaces

Berkovich's test relations (`IsNear`) for morphisms out of and into the chosen disjoint union
`localizedSigmaCofan` of a family of analytic spaces: gluing over the summands, maps missing
the test locus, and the position of test domains in a single summand. -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ## Maps missing the test locus -/

section Missing

variable {T B : SaturatedAtlasPresentation.{u, v, v} K}

/-- Two strong maps whose underlying maps both miss the test locus are near. -/
theorem strongNear_of_preimage_eq_empty {τ : TestTriple B} {a b : T ⟶ B}
    (ha : a.baseMap ⁻¹' τ.locus = ∅) (hb : b.baseMap ⁻¹' τ.locus = ∅) : StrongNear τ a b := by
  refine ⟨ha.trans hb.symm, fun y hy => ?_, fun i hi p => ?_⟩
  · rw [ha] at hy
    exact hy.elim
  · have hmem : T.presentation.atlas.chart i p ∈ a.baseMap ⁻¹' τ.locus :=
      hi.1 ⟨_, ⟨p, rfl⟩, rfl⟩
    rw [ha] at hmem
    exact hmem.elim

/-- Two localized morphisms whose underlying maps both miss the test locus are near. -/
theorem isNear_of_preimage_eq_empty {X Y : LocalizedCategory.{u, v, v} (K := K)}
    {τ : TestTriple (presentationOf X)} {φ ψ : Y ⟶ X}
    (hφ : (localizedSpaceFunctor.map φ : localizedSpaceFunctor.obj Y →
      localizedSpaceFunctor.obj X) ⁻¹' τ.locus = ∅)
    (hψ : (localizedSpaceFunctor.map ψ : localizedSpaceFunctor.obj Y →
      localizedSpaceFunctor.obj X) ⁻¹' τ.locus = ∅) : IsNear τ φ ψ := by
  obtain ⟨S, s, hs, a, b, ha, hb⟩ :=
    exists_commonStrongNumerators (T := presentationOf Y) (A := presentationOf X)
      (B := presentationOf X) φ ψ
  refine (isNear_iff_numerators τ φ ψ).2 ⟨S, s, hs, a, b, ha, hb, ?_⟩
  refine strongNear_of_preimage_eq_empty ?_ ?_
  · refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have hmem : s.baseMap x ∈ (localizedSpaceFunctor.map φ : localizedSpaceFunctor.obj Y →
        localizedSpaceFunctor.obj X) ⁻¹' τ.locus :=
      (congrArg (fun y : localizedSpaceFunctor.obj X => y ∈ τ.locus)
        (numerator_point_eq_of_fraction_equation s a φ ha x)).mpr hx
    exact Set.eq_empty_iff_forall_notMem.mp hφ _ hmem
  · refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have hmem : s.baseMap x ∈ (localizedSpaceFunctor.map ψ : localizedSpaceFunctor.obj Y →
        localizedSpaceFunctor.obj X) ⁻¹' τ.locus :=
      (congrArg (fun y : localizedSpaceFunctor.obj X => y ∈ τ.locus)
        (numerator_point_eq_of_fraction_equation s b ψ hb x)).mpr hx
    exact Set.eq_empty_iff_forall_notMem.mp hψ _ hmem

end Missing

/-! ## Charts of chosen disjoint unions -/

section SigmaCharts

variable {J : Type z} (S : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)

@[simp]
theorem sigmaCofan_inj_baseMap_apply (j : J) (x : (S j).presentation.space) :
    ((sigmaCofan S).inj j).baseMap x = (⟨j, x⟩ : (i : J) × (S i).presentation.space) := rfl

/-- The image of a chart of a component is a chart of the chosen disjoint union. -/
theorem exists_sigma_chart_eq_image (j : J)
    (i : (nonemptyReplacement (S j)).presentation.atlas.Index) :
    ∃ k : (sigmaCofan S).pt.presentation.atlas.Index,
      Set.range ((sigmaCofan S).pt.presentation.atlas.chart k) =
        ((sigmaCofan S).inj j).baseMap ''
          Set.range ((nonemptyReplacement (S j)).presentation.atlas.chart i) := by
  obtain ⟨D, hD⟩ := i.2
  let D' : IndexedAffinoidAtlas.LocalDomain
      (AtlasDisjointUnion.atlas (fun j => (nonemptyFamily S j).atlas)
        (nonemptyFamily_hasNonemptyCharts S)) := ⟨⟨j, D.index⟩, D.domain⟩
  refine ⟨⟨D'.locus, D', rfl⟩, ?_⟩
  rw [show Set.range ((sigmaCofan S).pt.presentation.atlas.chart ⟨D'.locus, D', rfl⟩) =
      D'.locus from IndexedAffinoidAtlas.range_saturatedChart _ _,
    show Set.range ((nonemptyReplacement (S j)).presentation.atlas.chart i) = i.1 from
      IndexedAffinoidAtlas.range_saturatedChart _ _, ← hD]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- Every test domain of a chosen disjoint union lies in a single component. -/
theorem TestTriple.exists_locus_subset_range_sigmaMk (τ : TestTriple (sigmaCofan S).pt) :
    ∃ j : J, τ.locus ⊆
      Set.range (Sigma.mk (β := fun i => ((S i).presentation.space : Type (max z v))) j) := by
  obtain ⟨D, hD⟩ := τ.domain.2
  refine ⟨D.index.1, fun y hy => ?_⟩
  have hy' : y ∈ τ.domain.1 := by
    have h : τ.locus = τ.domain.1 := IndexedAffinoidAtlas.range_saturatedChart _ _
    rwa [h] at hy
  rw [← hD] at hy'
  obtain ⟨z, -, rfl⟩ := hy'
  exact ⟨_, rfl⟩

/-- **Gluing of the strong test relation** over the components of a chosen disjoint union. -/
theorem StrongNear.of_sigma {B : SaturatedAtlasPresentation.{u, max z v, max z v} K}
    {τ : TestTriple B} {a b : (sigmaCofan S).pt ⟶ B}
    (h : ∀ j, StrongNear τ ((sigmaCofan S).inj j ≫ a) ((sigmaCofan S).inj j ≫ b)) :
    StrongNear τ a b := by
  refine ⟨?_, fun y hy => ?_, fun k hk p => ?_⟩
  · ext ⟨j, x⟩
    exact Set.ext_iff.mp (h j).1 x
  · obtain ⟨j, x⟩ := y
    obtain ⟨i, hi, hxi⟩ := (h j).2.1 x hy
    obtain ⟨k, hk⟩ := exists_sigma_chart_eq_image S j i
    refine ⟨k, ⟨?_, ?_⟩, (Set.ext_iff.mp hk _).mpr ⟨x, hxi, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨w', hw', rfl⟩ := (Set.ext_iff.mp hk w).mp hw
      exact hi.1 ⟨w', hw', rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨w', hw', rfl⟩ := (Set.ext_iff.mp hk w).mp hw
      exact hi.2 ⟨w', hw', rfl⟩
  · set y := (sigmaCofan S).pt.presentation.atlas.chart k p with hy
    obtain ⟨j, x⟩ := y
    obtain ⟨k₀, hk₀⟩ := exists_chart_mem (nonemptyReplacement (S j)) x
    obtain ⟨k', hxk', -, hk'k⟩ := exists_subchart_image_subset ((sigmaCofan S).inj j) k₀ hk₀ k
      ⟨p, hy.symm⟩
    obtain ⟨p', hp'⟩ := hxk'
    have hpk : BanachSpectrum.comap (((sigmaCofan S).inj j).pullback k' k hk'k).toBoundedRingHom
        p' = p := by
      apply ((sigmaCofan S).pt.presentation.atlas.isEmbedding_chart k).injective
      rw [((sigmaCofan S).inj j).chart_comm, hp']
      exact hy
    subst hpk
    have ha' : ((sigmaCofan S).inj j ≫ a).baseMap ''
        Set.range ((nonemptyReplacement (S j)).presentation.atlas.chart k') ⊆ τ.locus := by
      rintro _ ⟨w, hw, rfl⟩
      exact hk.1 ⟨_, hk'k ⟨w, hw, rfl⟩, rfl⟩
    have hb' : ((sigmaCofan S).inj j ≫ b).baseMap ''
        Set.range ((nonemptyReplacement (S j)).presentation.atlas.chart k') ⊆ τ.locus := by
      rintro _ ⟨w, hw, rfl⟩
      exact hk.2 ⟨_, hk'k ⟨w, hw, rfl⟩, rfl⟩
    have hbound := (h j).2.2 k' ⟨ha', hb'⟩ p'
    rw [comp_pullback_eq ((sigmaCofan S).inj j) a k' k τ.domain hk'k hk.1 ha',
      comp_pullback_eq ((sigmaCofan S).inj j) b k' k τ.domain hk'k hk.2 hb'] at hbound
    change p' ((((sigmaCofan S).inj j).pullback k' k hk'k)
      (a.pullback k τ.domain hk.1 τ.function - b.pullback k τ.domain hk.2 τ.function)) ≤
        τ.bound
    rw [map_sub]
    exact hbound

end SigmaCharts

/-! ## Gluing in the localized category -/

section LocalizedGluing

variable {J : Type z}

theorem localizationFunctor_map_nonemptyReplacementHom_comp_localizedSigmaCofan_inj
    (Xf : J → LocalizedCategory.{u, max z v, max z v} (K := K)) (j : J) :
    localizationFunctor.map (nonemptyReplacementHom (localizedObjectEquiv.symm (Xf j))) ≫
      (localizedSigmaCofan Xf).inj j =
        localizationFunctor.map
          ((sigmaCofan fun j => localizedObjectEquiv.symm (Xf j)).inj j) :=
  Localization.isoOfHom_hom_inv_id_assoc (L := localizationFunctor)
    (W := quasiIsomorphisms (K := K)) _ (isQuasiIso_nonemptyReplacementHom _) _

/-- **Gluing of the test relation** over the summands of a disjoint union of analytic
spaces. -/
theorem isNear_of_localizedSigmaCofan
    (Xf : J → LocalizedCategory.{u, max z v, max z v} (K := K))
    {Z : LocalizedCategory.{u, max z v, max z v} (K := K)}
    (τ : TestTriple (presentationOf Z)) (φ ψ : (localizedSigmaCofan Xf).pt ⟶ Z)
    (h : ∀ j, IsNear τ ((localizedSigmaCofan Xf).inj j ≫ φ)
      ((localizedSigmaCofan Xf).inj j ≫ ψ)) : IsNear τ φ ψ := by
  let F : J → SaturatedAtlasPresentation.{u, max z v, max z v} K :=
    fun j => localizedObjectEquiv.symm (Xf j)
  have h' : ∀ j, ∃ (T : SaturatedAtlasPresentation.{u, max z v, max z v} K)
      (s : T ⟶ nonemptyReplacement (F j)) (_ : s.IsQuasiIso) (a b : T ⟶ presentationOf Z),
      localizationFunctor.map s ≫ localizationFunctor.map ((sigmaCofan F).inj j) ≫ φ =
        localizationFunctor.map a ∧
      localizationFunctor.map s ≫ localizationFunctor.map ((sigmaCofan F).inj j) ≫ ψ =
        localizationFunctor.map b ∧ StrongNear τ a b := by
    intro j
    have hj : IsNear τ (localizationFunctor.map ((sigmaCofan F).inj j) ≫ φ)
        (localizationFunctor.map ((sigmaCofan F).inj j) ≫ ψ) := by
      convert (h j).precomp
        (localizationFunctor.map (nonemptyReplacementHom (localizedObjectEquiv.symm (Xf j))))
        using 1
      · exact ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ φ)
          (localizationFunctor_map_nonemptyReplacementHom_comp_localizedSigmaCofan_inj
            Xf j))).symm
      · exact ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ ψ)
          (localizationFunctor_map_nonemptyReplacementHom_comp_localizedSigmaCofan_inj
            Xf j))).symm
    exact (isNear_iff_numerators τ _ _).1 hj
  choose T s hs a b ha hb hab using h'
  let sS : (sigmaCofan T).pt ⟶ (sigmaCofan F).pt :=
    Cofan.IsColimit.desc (isColimitSigmaCofan T)
      fun j => (nonemptyReplacementHom (T j) ≫ s j) ≫ (sigmaCofan F).inj j
  have hsS : sS.IsQuasiIso :=
    isQuasiIso_sigmaCofan_desc T F (fun j => nonemptyReplacementHom (T j) ≫ s j)
      fun j => (quasiIsomorphisms (K := K)).comp_mem _ _
        (isQuasiIso_nonemptyReplacementHom _) (hs j)
  let aS : (sigmaCofan T).pt ⟶ presentationOf Z :=
    Cofan.IsColimit.desc (isColimitSigmaCofan T) fun j => nonemptyReplacementHom (T j) ≫ a j
  let bS : (sigmaCofan T).pt ⟶ presentationOf Z :=
    Cofan.IsColimit.desc (isColimitSigmaCofan T) fun j => nonemptyReplacementHom (T j) ≫ b j
  have hsj : ∀ j, (sigmaCofan T).inj j ≫ sS =
      (nonemptyReplacementHom (T j) ≫ s j) ≫ (sigmaCofan F).inj j :=
    fun j => Cofan.IsColimit.fac _ _ j
  have haj : ∀ j, (sigmaCofan T).inj j ≫ aS = nonemptyReplacementHom (T j) ≫ a j :=
    fun j => Cofan.IsColimit.fac _ _ j
  have hbj : ∀ j, (sigmaCofan T).inj j ≫ bS = nonemptyReplacementHom (T j) ≫ b j :=
    fun j => Cofan.IsColimit.fac _ _ j
  have hsS_map : ∀ j, localizationFunctor.map ((sigmaCofan T).inj j) ≫
      localizationFunctor.map sS = localizationFunctor.map (nonemptyReplacementHom (T j)) ≫
        (localizationFunctor.map (s j) ≫ localizationFunctor.map ((sigmaCofan F).inj j)) :=
    fun j => by rw [← Functor.map_comp, hsj, Functor.map_comp, Functor.map_comp, Category.assoc]
  have haS_map : ∀ j, localizationFunctor.map ((sigmaCofan T).inj j) ≫
      localizationFunctor.map aS =
        localizationFunctor.map (nonemptyReplacementHom (T j)) ≫ localizationFunctor.map (a j) :=
    fun j => by rw [← Functor.map_comp, haj, Functor.map_comp]
  have hbS_map : ∀ j, localizationFunctor.map ((sigmaCofan T).inj j) ≫
      localizationFunctor.map bS =
        localizationFunctor.map (nonemptyReplacementHom (T j)) ≫ localizationFunctor.map (b j) :=
    fun j => by rw [← Functor.map_comp, hbj, Functor.map_comp]
  refine (isNear_iff_numerators τ φ ψ).2 ⟨(sigmaCofan T).pt, sS, hsS, aS, bS, ?_, ?_, ?_⟩
  · refine (rightFractionCoproducts K J).hom_ext localizationFunctor T _ _ fun j => ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ φ) (hsS_map j)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun m => localizationFunctor.map (nonemptyReplacementHom (T j)) ≫ m)
            ((Category.assoc _ _ _).trans (ha j))).trans (haS_map j).symm)))
  · refine (rightFractionCoproducts K J).hom_ext localizationFunctor T _ _ fun j => ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ ψ) (hsS_map j)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun m => localizationFunctor.map (nonemptyReplacementHom (T j)) ≫ m)
            ((Category.assoc _ _ _).trans (hb j))).trans (hbS_map j).symm)))
  · refine StrongNear.of_sigma T fun j => ?_
    rw [haj, hbj]
    exact (hab j).precomp _

/-- The underlying map of the inclusion of a summand is the sigma injection. -/
theorem localizedSpaceFunctor_map_localizedSigmaCofan_inj
    (Xf : J → LocalizedCategory.{u, max z v, max z v} (K := K)) (j : J)
    (x : (presentationOf (Xf j)).presentation.space) :
    localizedSpaceFunctor.map ((localizedSigmaCofan Xf).inj j) x =
      (⟨j, x⟩ : (i : J) × (presentationOf (Xf i)).presentation.space) :=
  numerator_point_eq_of_fraction_equation (nonemptyReplacementHom (localizedObjectEquiv.symm (Xf j)))
    ((sigmaCofan fun j => localizedObjectEquiv.symm (Xf j)).inj j) ((localizedSigmaCofan Xf).inj j)
    (localizationFunctor_map_nonemptyReplacementHom_comp_localizedSigmaCofan_inj Xf j) x

/-- Every test domain of a disjoint union of analytic spaces lies in a single summand. -/
theorem TestTriple.exists_locus_subset_range_localizedSigmaCofan
    (Xf : J → LocalizedCategory.{u, max z v, max z v} (K := K))
    (τ : TestTriple (presentationOf (localizedSigmaCofan Xf).pt)) :
    ∃ j : J, τ.locus ⊆ Set.range
      (Sigma.mk (β := fun i => ((presentationOf (Xf i)).presentation.space : Type (max z v))) j) :=
  TestTriple.exists_locus_subset_range_sigmaMk (fun j => presentationOf (Xf j)) τ

/-- The preimage of a test domain under the inclusion of a summand is compact. -/
theorem isCompact_preimage_localizedSigmaCofan_inj
    (Xf : J → LocalizedCategory.{u, max z v, max z v} (K := K)) (j : J)
    (τ : TestTriple (presentationOf (localizedSigmaCofan Xf).pt)) :
    IsCompact ((localizedSpaceFunctor.map ((localizedSigmaCofan Xf).inj j) :
      localizedSpaceFunctor.obj (Xf j) → localizedSpaceFunctor.obj (localizedSigmaCofan Xf).pt) ⁻¹'
        τ.locus) := by
  have h : (localizedSpaceFunctor.map ((localizedSigmaCofan Xf).inj j) :
      localizedSpaceFunctor.obj (Xf j) → localizedSpaceFunctor.obj (localizedSigmaCofan Xf).pt) =
        Sigma.mk (β := fun i => ((presentationOf (Xf i)).presentation.space : Type (max z v))) j :=
    funext (localizedSpaceFunctor_map_localizedSigmaCofan_inj Xf j)
  rw [h]
  exact IsClosedEmbedding.sigmaMk.isCompact_preimage τ.isCompact_locus

/-- A morphism through the inclusion of a summand misses every test domain lying in another
summand. -/
theorem preimage_locus_comp_localizedSigmaCofan_inj_eq_empty
    (Xf : J → LocalizedCategory.{u, max z v, max z v} (K := K))
    {W : LocalizedCategory.{u, max z v, max z v} (K := K)} {j j₀ : J} (hj : j ≠ j₀)
    (f : W ⟶ Xf j) (τ : TestTriple (presentationOf (localizedSigmaCofan Xf).pt))
    (hτ : τ.locus ⊆ Set.range
      (Sigma.mk (β := fun i => ((presentationOf (Xf i)).presentation.space : Type (max z v))) j₀)) :
    (localizedSpaceFunctor.map (f ≫ (localizedSigmaCofan Xf).inj j) :
      localizedSpaceFunctor.obj W → localizedSpaceFunctor.obj (localizedSigmaCofan Xf).pt) ⁻¹'
        τ.locus = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨y, hy⟩ := hτ (Set.mem_preimage.mp hx)
  have h2 : localizedSpaceFunctor.map (f ≫ (localizedSigmaCofan Xf).inj j) x =
      (⟨j, localizedSpaceFunctor.map f x⟩ :
        (i : J) × (presentationOf (Xf i)).presentation.space) := by
    rw [Functor.map_comp]
    exact localizedSpaceFunctor_map_localizedSigmaCofan_inj Xf j _
  exact hj (congrArg Sigma.fst (hy.trans h2)).symm

end LocalizedGluing

end Langlands.Analytic.SaturatedAtlasPresentation
