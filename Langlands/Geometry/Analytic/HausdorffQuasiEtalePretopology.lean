import Langlands.Geometry.Analytic.CompactProbeQuasiEtaleHausdorffComparisonProof
import Langlands.Geometry.Analytic.EquivariantCompactProbeTopology
import Langlands.Geometry.Analytic.EquivariantQuasiEtalePullbacksProof
import Langlands.Geometry.Analytic.GroundFieldExtensionHausdorff
import Langlands.Geometry.Analytic.CompatibleLocalizedFieldPoints
import Langlands.Geometry.Analytic.QuasiEtaleFieldPointPullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.Pretopology

/-! # The quasi-étale pretopology on Hausdorff analytic source objects -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Filter _root_.Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (X : LocalizedCategory.{u, v, v} (K := K))

/-- The full subcategory of quasi-étale over-objects with Hausdorff source. -/
def hausdorffQuasiEtaleProperty : ObjectProperty (QuasiEtaleSite X) :=
  fun U => hausdorffProperty U.left

/-- Quasi-étale source objects with Hausdorff underlying spaces. -/
abbrev HausdorffQuasiEtaleSite := (hausdorffQuasiEtaleProperty X).FullSubcategory

/-- Covering families are the original finite chart-neighbourhood families. -/
def hausdorffQuasiEtalePrecoverage : Precoverage (HausdorffQuasiEtaleSite X) :=
  (quasiEtalePrecoverage X).comap (hausdorffQuasiEtaleProperty X).ι

namespace HausdorffQuasiEtaleSite

variable {X}

/-- A morphism of Hausdorff quasi-étale source objects is quasi-étale. -/
theorem quasiEtale_left {U V : HausdorffQuasiEtaleSite X} (f : U ⟶ V) : quasiEtale f.hom.left := by
  let : T2Space (localizedSpaceFunctor.obj U.obj.left) := U.property
  let : T2Space (localizedSpaceFunctor.obj V.obj.left) := V.property
  exact quasiEtale_of_over_of_t2Space V.obj.prop ((MorphismProperty.Over.w f.hom).symm ▸ U.obj.prop)

private abbrev underlying : HausdorffQuasiEtaleSite X ⥤ LocalizedCategory.{u, v, v} (K := K) :=
  (hausdorffQuasiEtaleProperty X).ι ⋙
    MorphismProperty.Over.forget (quasiEtale (K := K)) ⊤ X ⋙ Over.forget X

/-- The underlying analytic pullback gives the full Hausdorff site pullback. -/
theorem pullback_of_left {A B U W : HausdorffQuasiEtaleSite X}
    {f : A ⟶ U} {g : B ⟶ U} {p : W ⟶ A} {q : W ⟶ B}
    (h : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left) :
    IsPullback p q f g :=
  IsPullback.of_map_of_faithful (underlying (X := X)) h

/-- The actual analytic pullback of a Hausdorff site cospan has a Hausdorff
quasi-étale structure over the base. -/
theorem exists_analyticPullback {A B U : HausdorffQuasiEtaleSite X} (f : A ⟶ U) (g : B ⟶ U) :
    ∃ (W : HausdorffQuasiEtaleSite X) (p : W ⟶ A) (q : W ⟶ B),
      IsPullback p.hom.left q.hom.left f.hom.left g.hom.left := by
  let : T2Space (localizedSpaceFunctor.obj A.obj.left) := A.property
  let : T2Space (localizedSpaceFunctor.obj B.obj.left) := B.property
  let : T2Space (localizedSpaceFunctor.obj U.obj.left) := U.property
  have hf := quasiEtale_left f
  obtain ⟨P, p, q, hp⟩ := exists_localizedPullback_of_quasiEtale f.hom.left g.hom.left hf
  have hP : quasiEtale (q ≫ B.obj.hom) :=
    MorphismProperty.Over.w g.hom ▸
      quasiEtale_common_of_isPullback_over hp U.obj.prop
        ((MorphismProperty.Over.w f.hom).symm ▸ A.obj.prop)
        ((MorphismProperty.Over.w g.hom).symm ▸ B.obj.prop)
  let W : HausdorffQuasiEtaleSite X :=
    ⟨MorphismProperty.Over.mk ⊤ (q ≫ B.obj.hom) hP, (hasCompactPairPreimages_of_quasiEtale hp hf).1⟩
  have hπ : p ≫ A.obj.hom = q ≫ B.obj.hom := by
    rw [← MorphismProperty.Over.w f.hom, ← MorphismProperty.Over.w g.hom,
      ← Category.assoc, ← Category.assoc, hp.w]
  exact ⟨W, ObjectProperty.homMk (MorphismProperty.Over.homMk p hπ),
    ObjectProperty.homMk (MorphismProperty.Over.homMk q rfl), hp⟩

instance : HasPullbacks (HausdorffQuasiEtaleSite X) :=
  @hasPullbacks_of_hasLimit_cospan _ _ (fun {_ _ _ f g} => by
    obtain ⟨W, p, q, h⟩ := exists_analyticPullback f g
    exact (pullback_of_left h).hasPullback)

/-- The underlying square of an arbitrary Hausdorff site pullback is an
analytic pullback. -/
theorem isPullback_left {A B U W : HausdorffQuasiEtaleSite X}
    {f : A ⟶ U} {g : B ⟶ U} {p : W ⟶ A} {q : W ⟶ B} (h : IsPullback p q f g) :
    IsPullback p.hom.left q.hom.left f.hom.left g.hom.left := by
  let F := underlying (X := X)
  obtain ⟨W', p', q', hW'⟩ := exists_analyticPullback f g
  have hW := pullback_of_left hW'
  have hF : IsPullback (F.map p') (F.map q') (F.map f) (F.map g) := hW'
  let : PreservesLimit (cospan f g) F := preservesLimit_of_preserves_limit_cone hW.isLimit
    ((isLimitMapConePullbackConeEquiv F hW.w).symm hF.isLimit)
  exact h.map F

local notation "pts" => _root_.CategoryTheory.Functor.obj localizedSpaceFunctor
local notation "pt" => _root_.CategoryTheory.Functor.map localizedSpaceFunctor

/-- An indexed family covers precisely when its actual chart images
form the finite point neighbourhoods in the quasi-étale definition. -/
theorem ofArrows_mem_precoverage_iff {U : HausdorffQuasiEtaleSite X} {ι : Type w}
    {V : ι → HausdorffQuasiEtaleSite X} (f : ∀ i, V i ⟶ U) :
    Presieve.ofArrows V f ∈ hausdorffQuasiEtalePrecoverage X U ↔
      ∀ x : pts U.obj.left, ∃ σ : Set (Set (pts U.obj.left)), σ.Finite ∧ ⋃₀ σ ∈ 𝓝 x ∧
        ∀ T ∈ σ, ∃ (i : ι) (j : (presentationOf (V i).obj.left).presentation.atlas.Index),
          T = pt (f i).hom.left '' range ((presentationOf (V i).obj.left).presentation.atlas.chart j) := by
  change (Presieve.ofArrows V f).map (hausdorffQuasiEtaleProperty X).ι ∈ quasiEtalePrecoverage X U.obj ↔ _
  rw [Presieve.map_ofArrows, mem_quasiEtalePrecoverage_iff]
  constructor
  · intro h x
    obtain ⟨σ, hσ, hn, hc⟩ := h x
    refine ⟨σ, hσ, hn, ?_⟩
    intro T hT
    obtain ⟨A, a, j, ha, hr⟩ := hc T hT
    cases ha with
    | mk i => exact ⟨i, j, hr⟩
  · intro h x
    obtain ⟨σ, hσ, hn, hc⟩ := h x
    refine ⟨σ, hσ, hn, ?_⟩
    intro T hT
    obtain ⟨i, j, hr⟩ := hc T hT
    exact ⟨(V i).obj, (f i).hom, j, ⟨i⟩, hr⟩

private theorem exists_compatible_point {A B U P : LocalizedCategory.{u, v, v} (K := K)}
    {a : A ⟶ U} {b : B ⟶ U} {p : P ⟶ A} {q : P ⟶ B}
    (h : IsPullback p q a b) (ha : quasiEtale a)
    (x : pts A) (y : pts B) (he : pt a x = pt b y) :
    ∃ z : pts P, pt p z = x ∧ pt q z = y := by
  obtain ⟨L, _, _, _, _, _, x', y', hx, hy, hxy⟩ := exists_compatible_localizedFieldPoints a b x y he
  obtain ⟨z, hp, hq⟩ := Types.exists_of_isPullback
    (localizedFieldPoint_isPullback_of_quasiEtale (L := L) h ha) x' y' hxy
  refine ⟨((localizedFieldPointProjection L).app P z).down, ?_, ?_⟩
  · rw [← localizedFieldPointProjection_map_down, hp, hx]
  · rw [← localizedFieldPointProjection_map_down, hq, hy]

private theorem cover_compact_pullback_piece
    {A B U P : LocalizedCategory.{u, v, v} (K := K)}
    [T2Space (pts A)] [T2Space (pts B)] [T2Space (pts U)]
    {a : A ⟶ U} {b : B ⟶ U} {p : P ⟶ A} {q : P ⟶ B}
    (h : IsPullback p q a b) (ha : quasiEtale a)
    {C : Set (pts A)} {N : Set (pts B)} (hC : IsCompact C) (hN : IsCompact N) :
    ∃ σ : Set (Set (pts P)), σ.Finite ∧
      σ ⊆ range (fun i => range ((presentationOf P).presentation.atlas.chart i)) ∧
      N ∩ (pt b ⁻¹' (pt a '' C)) ⊆ ⋃₀ (Set.image (pt q) '' σ) := by
  let Z : Set (pts A × pts B) := (C ×ˢ N) ∩ {z | pt a z.1 = pt b z.2}
  have hZ : IsCompact Z := (hC.prod hN).of_isClosed_subset
    (IsClosed.inter (hC.prod hN).isClosed (isClosed_eq
      ((pt a).hom.continuous.comp continuous_fst)
      ((pt b).hom.continuous.comp continuous_snd))) inter_subset_left
  have hL := (hasCompactPairPreimages_of_quasiEtale h ha).2 Z hZ (fun _ hz => hz.2)
  obtain ⟨σ, hσ, hs, hcov⟩ :=
    (presentationOf P).presentation.atlas.isNet_chartFamily.1.exists_finite_cover_of_isCompact hL
  refine ⟨σ, hσ, hs, ?_⟩
  rintro y ⟨hy, x, hx, hxy⟩
  obtain ⟨z, hp, hq⟩ := exists_compatible_point h ha x y hxy
  have hz : z ∈ localizedProjectionPair p q ⁻¹' Z := by
    change (pt p z, pt q z) ∈ Z
    rw [hp, hq]
    exact ⟨⟨hx, hy⟩, hxy⟩
  obtain ⟨T, hT, hzT⟩ := mem_sUnion.mp (hcov hz)
  exact mem_sUnion.mpr ⟨_, ⟨T, hT, rfl⟩, z, hzT, hq⟩

instance : (hausdorffQuasiEtalePrecoverage X).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} U V f hf W g P p q hp := by
    rw [ofArrows_mem_precoverage_iff] at hf ⊢
    intro x
    let b := g.hom.left
    obtain ⟨σ, hσ, hn, hs⟩ := hf (pt b x)
    let : WeaklyLocallyCompactSpace (pts W.obj.left) := weaklyLocallyCompactSpace_localized _
    obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x
    have hpiece (T : Set (pts U.obj.left)) (hT : T ∈ σ) :
        ∃ δ : Set (Set (pts W.obj.left)), δ.Finite ∧
          N ∩ (pt b ⁻¹' T) ⊆ ⋃₀ δ ∧
          ∀ S ∈ δ, ∃ (i : ι) (j : (presentationOf (P i).obj.left).presentation.atlas.Index),
            S = pt (p i).hom.left '' range ((presentationOf (P i).obj.left).presentation.atlas.chart j) := by
      obtain ⟨i, j, rfl⟩ := hs T hT
      let : T2Space (pts U.obj.left) := U.property
      let : T2Space (pts (V i).obj.left) := (V i).property
      let : T2Space (pts W.obj.left) := W.property
      have hC := ((presentationOf (V i).obj.left).isCompactDomain_chartDomain j).1
      obtain ⟨τ, hτ, hchart, hcov⟩ :=
        cover_compact_pullback_piece (isPullback_left (hp i)).flip (quasiEtale_left (f i)) hC hN
      refine ⟨Set.image (pt (p i).hom.left) '' τ, hτ.image _, hcov, ?_⟩
      rintro _ ⟨S, hS, rfl⟩
      obtain ⟨k, rfl⟩ := hchart hS
      exact ⟨i, k, rfl⟩
    choose! δ hfδ hsub hδ using hpiece
    refine ⟨⋃ T ∈ σ, δ T, hσ.biUnion hfδ, ?_, ?_⟩
    · refine Filter.mem_of_superset
        (Filter.inter_mem hNx ((pt b).hom.continuous.continuousAt.preimage_mem_nhds hn)) ?_
      rintro y ⟨hyN, T, hT, hyT⟩
      obtain ⟨S, hS, hyS⟩ := mem_sUnion.mp (hsub T hT ⟨hyN, hyT⟩)
      exact mem_sUnion.mpr ⟨S, mem_iUnion₂.mpr ⟨T, hT, hS⟩, hyS⟩
    · intro S hS
      obtain ⟨T, hT, hST⟩ := mem_iUnion₂.mp hS
      exact hδ T hT S hST

private theorem finite_chart_images_cover_compact {U : HausdorffQuasiEtaleSite X} {ι : Type w}
    {V : ι → HausdorffQuasiEtaleSite X} (f : ∀ i, V i ⟶ U)
    (hf : Presieve.ofArrows V f ∈ hausdorffQuasiEtalePrecoverage X U)
    {C : Set (pts U.obj.left)} (hC : IsCompact C) :
    ∃ σ : Set (Set (pts U.obj.left)), σ.Finite ∧ C ⊆ ⋃₀ σ ∧
      ∀ T ∈ σ, ∃ (i : ι) (j : (presentationOf (V i).obj.left).presentation.atlas.Index),
        T = pt (f i).hom.left '' range ((presentationOf (V i).obj.left).presentation.atlas.chart j) := by
  classical
  choose σ hfσ hnhds hchart using (ofArrows_mem_precoverage_iff f).mp hf
  obtain ⟨s, hs⟩ := hC.elim_nhds_subcover' (fun x _ => ⋃₀ σ x) (fun x _ => hnhds x)
  refine ⟨⋃ x : s, σ x.val.val, Set.finite_iUnion fun x => hfσ x.val.val, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, T, hT, hyT⟩ := mem_iUnion₂.mp (hs hy)
    exact mem_sUnion.mpr ⟨T, mem_iUnion.mpr ⟨⟨x, hx⟩, hT⟩, hyT⟩
  · intro T hT
    obtain ⟨x, hx⟩ := mem_iUnion.mp hT
    exact hchart x.val.val T hx

instance : (hausdorffQuasiEtalePrecoverage X).IsStableUnderComposition where
  comp_mem_coverings {ι} U V f hf σ W g hg := by
    rw [ofArrows_mem_precoverage_iff] at hf ⊢
    intro x
    obtain ⟨τ, hτ, hn, hs⟩ := hf x
    have hpiece (T : Set (pts U.obj.left)) (hT : T ∈ τ) :
        ∃ δ : Set (Set (pts U.obj.left)), δ.Finite ∧ T ⊆ ⋃₀ δ ∧
          ∀ S ∈ δ, ∃ (i : Σ i, σ i) (j : (presentationOf (W i.1 i.2).obj.left).presentation.atlas.Index),
            S = pt ((g i.1 i.2) ≫ f i.1).hom.left ''
              range ((presentationOf (W i.1 i.2).obj.left).presentation.atlas.chart j) := by
      obtain ⟨i, j, rfl⟩ := hs T hT
      let a := pt (f i).hom.left
      have hC := ((presentationOf (V i).obj.left).isCompactDomain_chartDomain j).1
      obtain ⟨δ, hδ, hcov, hchart⟩ := finite_chart_images_cover_compact (g i) (hg i) hC
      refine ⟨Set.image a '' δ, hδ.image _, ?_, ?_⟩
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨S, hS, hyS⟩ := mem_sUnion.mp (hcov hy)
        exact mem_sUnion.mpr ⟨_, ⟨S, hS, rfl⟩, y, hyS, rfl⟩
      · rintro _ ⟨S, hS, rfl⟩
        obtain ⟨l, k, rfl⟩ := hchart S hS
        refine ⟨⟨i, l⟩, k, ?_⟩
        rw [Set.image_image]
        change _ = pt ((g i l).hom.left ≫ (f i).hom.left) '' _
        rw [_root_.CategoryTheory.Functor.map_comp]
        rfl
    choose! δ hfin hcov hchart using hpiece
    refine ⟨⋃ T ∈ τ, δ T, hτ.biUnion hfin, Filter.mem_of_superset hn ?_, ?_⟩
    · rintro y ⟨T, hT, hyT⟩
      obtain ⟨S, hS, hyS⟩ := mem_sUnion.mp (hcov T hT hyT)
      exact mem_sUnion.mpr ⟨S, mem_iUnion₂.mpr ⟨T, hT, hS⟩, hyS⟩
    · intro S hS
      obtain ⟨T, hT, hST⟩ := mem_iUnion₂.mp hS
      exact hchart T hT S hST

instance : (hausdorffQuasiEtalePrecoverage X).HasIsos where
  mem_coverings_of_isIso {U V} f hf := by
    rw [← Presieve.ofArrows_pUnit.{0} f, ofArrows_mem_precoverage_iff]
    let F := underlying (X := X) ⋙ localizedSpaceFunctor
    let e : pts U.obj.left ≃ₜ pts V.obj.left := TopCat.homeoOfIso (F.mapIso (asIso f))
    intro x
    obtain ⟨σ, hσ, hs, _, hn⟩ := (presentationOf U.obj.left).presentation.atlas.isNet_chartFamily.1 (e.symm x)
    refine ⟨Set.image e '' σ, hσ.image _, ?_, ?_⟩
    · have hm : e '' ⋃₀ σ ∈ 𝓝 x := e.apply_symm_apply x ▸ e.isOpenMap.image_mem_nhds hn
      exact Set.image_sUnion ▸ hm
    · rintro _ ⟨T, hT, rfl⟩
      obtain ⟨j, rfl⟩ := hs hT
      exact ⟨PUnit.unit, j, rfl⟩

end HausdorffQuasiEtaleSite

/-- The chart-neighbourhood families form a pretopology on Hausdorff
quasi-étale over-objects. -/
def hausdorffQuasiEtalePretopology : Pretopology (HausdorffQuasiEtaleSite X) :=
  (hausdorffQuasiEtalePrecoverage X).toPretopology

/-- The chart-neighbourhood pretopology and its precoverage generate the same topology. -/
theorem hausdorffQuasiEtalePretopology_toGrothendieck :
    (hausdorffQuasiEtalePretopology X).toGrothendieck =
      (hausdorffQuasiEtalePrecoverage X).toGrothendieck :=
  (hausdorffQuasiEtalePrecoverage X).toGrothendieck_toPretopology_eq_toGrothendieck

/-- The Hausdorff chart pretopology has the covering sieves induced by the
compact-probe topology on all quasi-étale over-objects. -/
theorem mem_hausdorffQuasiEtaleTopology_iff_compactProbe
    {U : HausdorffQuasiEtaleSite X} (S : Sieve U) :
    S ∈ (hausdorffQuasiEtalePretopology X).toGrothendieck U ↔
      S.functorPushforward (hausdorffQuasiEtaleProperty X).ι ∈ compactProbeQuasiEtaleTopology X U.obj := by
  let F := (hausdorffQuasiEtaleProperty X).ι
  have hmap : Sieve.generate (S.arrows.map F) = S.functorPushforward F :=
    (Sieve.generate_map_eq_functorPushforward F).trans
      (congrArg (Sieve.functorPushforward F) (Sieve.generate_sieve S))
  rw [Pretopology.mem_toGrothendieck,
    compactProbeQuasiEtaleHausdorffComparison K X U.obj _ U.property,
    ← hmap, hasQuasiEtaleChartNeighborhoods_generate_iff]
  constructor
  · rintro ⟨R, hR, hRS⟩ x
    obtain ⟨σ, hσ, hn, hc⟩ := (mem_quasiEtalePrecoverage_iff (X := X)).mp hR x
    refine ⟨σ, hσ, hn, fun T hT => ?_⟩
    obtain ⟨V, f, i, hf, hTf⟩ := hc T hT
    exact ⟨V, f, i, Presieve.map_monotone (F := F) hRS _ _ hf, hTf⟩
  · exact fun h => ⟨S.arrows, mem_quasiEtalePrecoverage_iff.mpr h, le_rfl⟩

instance hausdorffQuasiEtaleInclusion_isCoverDense :
    (hausdorffQuasiEtaleProperty X).ι.IsCoverDense (compactProbeQuasiEtaleTopology X) where
  is_cover U := by
    intro C g hC
    let D : HausdorffQuasiEtaleSite X := ⟨C, hC.2⟩
    refine ⟨1, fun _ => C, fun _ => 𝟙 C, fun _ => hC, fun _ => ?_, fun x => ⟨0, x, ?_⟩⟩
    · change Presieve.coverByImage (hausdorffQuasiEtaleProperty X).ι U (𝟙 C ≫ g)
      exact ⟨⟨D, 𝟙 C, g, rfl⟩⟩
    · exact ConcreteCategory.congr_hom ((compactProbePointFunctor X).map_id C) x

/-- Hausdorff quasi-étale objects form a dense subsite of the full
compact-probe site. Each compact Hausdorff probe already belongs to it. -/
instance hausdorffQuasiEtaleInclusion_isDenseSubsite :
    (hausdorffQuasiEtaleProperty X).ι.IsDenseSubsite
      (hausdorffQuasiEtalePretopology X).toGrothendieck (compactProbeQuasiEtaleTopology X) where
  functorPushforward_mem_iff := (mem_hausdorffQuasiEtaleTopology_iff_compactProbe X _).symm

end Langlands.Analytic.SaturatedAtlasPresentation
