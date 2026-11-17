import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionEtaleAnalyticIsoStatement

/-! # Étale maps are local analytic isomorphisms of the varying-dimension atlases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-! ### Étale maps and monomorphisms -/

/-- If the composite of a natural transformation with a monomorphism is étale,
the transformation itself is étale: every represented pullback of it is a
represented pullback of the composite. -/
theorem IsEtale.of_comp_mono {S : Scheme.{u}} {F G H : Presheaf S} (g : F ⟶ G) (i : G ⟶ H)
    [Mono i] (h : IsEtale (g ≫ i)) : IsEtale g := by
  have hsq : ∀ {a : Over S} (t : (schemeYoneda S).obj a ⟶ G),
      IsPullback t (𝟙 _) i (t ≫ i) :=
    fun t => IsPullback.of_vert_isIso_mono ⟨by simp⟩
  refine ⟨fun a t => ?_, fun a b t fst snd hp => ?_⟩
  · obtain ⟨b, snd, fst, hp⟩ := h.1 (t ≫ i)
    refine ⟨b, snd, fst, ?_⟩
    have e : fst ≫ g = (schemeYoneda S).map snd ≫ t := by
      rw [← cancel_mono i]
      simpa only [Category.assoc] using hp.w
    exact (IsPullback.paste_vert_iff (hsq t) e).1 (by simpa only [Category.comp_id] using hp)
  · exact h.2 (t ≫ i) fst snd (by simpa only [Category.comp_id] using hp.paste_vert (hsq t))

namespace SmoothDimensionPieces

section Field

variable {K : Type u} [Field K] {X Y : AlgebraicSpace (Spec (CommRingCat.of K))}
  (hX : SmoothOverBase X) (hY : SmoothOverBase Y) {f : X ⟶ Y} (hf : IsEtaleMorphism f)

include hf in
/-- An étale morphism preserves the intrinsic dimension at every ordinary point:
composing the chosen smooth atlas of `X` with `f` gives an étale chart of `Y`
with the same local relative dimension. -/
theorem pointDimension_map_of_isEtaleMorphism (p : Points X.presheaf) :
    pointDimension hY (Points.map (hom f) p) = pointDimension hX p := by
  obtain ⟨u, rfl⟩ := surjective_chartPointMap (atlasMap hX) (atlasMap_isSurjective hX) p
  have h1 := pointDimension_chart hX (atlasMap hX) (atlasMap_isEtale hX) u
  have h2 := pointDimension_chart hY (atlasMap hX ≫ hom f)
    (hf _ _ (atlasMap_isEtale hX)) u
  have he : chartPointMap (atlasMap hX ≫ hom f) u =
      Points.map (hom f) (chartPointMap (atlasMap hX) u) := by
    simp only [chartPointMap, Function.comp_apply, Points.map_comp]
  rw [he] at h2
  exact_mod_cast h2.trans h1.symm

include hf in
/-- An étale morphism preserves the intrinsic dimension of field-valued sections. -/
theorem fieldPointDimension_map_of_isEtaleMorphism
    {L : Type u} [Field L] [Algebra K L] (x : RingPoints K X L) :
    fieldPointDimension hY (RingPoints.map f x) = fieldPointDimension hX x := by
  have key : uliftYonedaEquiv.{u + 1}.symm (RingPoints.map f x) =
      uliftYonedaEquiv.{u + 1}.symm x ≫ hom f :=
    (uliftYonedaEquiv_symm_comp.{u + 1} x (hom f)).symm
  unfold fieldPointDimension
  rw [key]
  have he : chartPointMap (uliftYonedaEquiv.{u + 1}.symm x ≫ hom f)
      (IsLocalRing.closedPoint L) =
      Points.map (hom f) (chartPointMap (uliftYonedaEquiv.{u + 1}.symm x)
        (IsLocalRing.closedPoint L)) :=
    Points.map_comp _ _ (schemePoint (ringTest K L) (IsLocalRing.closedPoint L))
  rw [he]
  exact pointDimension_map_of_isEtaleMorphism hX hY hf _

include hf in
/-- The point locus of a target piece pulls back to the source piece. -/
theorem preimage_subset_of_isEtaleMorphism (n : ℕ) :
    Points.map (hom f) ⁻¹' subset hY n = subset hX n := by
  ext p
  simp only [Set.mem_preimage, subset, Set.mem_singleton_iff,
    pointDimension_map_of_isEtaleMorphism hX hY hf]

include hf in
theorem range_le_of_isEtaleMorphism (n : ℕ) :
    Subfunctor.range ((PointOpenSubspace.subfunctor X.presheaf (subset hX n)).ι ≫ hom f) ≤
      PointOpenSubspace.subfunctor Y.presheaf (subset hY n) := by
  rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff,
    PointOpenSubspace.preimage, preimage_subset_of_isEtaleMorphism hX hY hf]

/-- The actual restriction of an étale morphism to the dimension-`n` pieces. -/
def etaleRestriction (n : ℕ) : space hX n ⟶ space hY n :=
  homMk (Subfunctor.lift ((PointOpenSubspace.subfunctor X.presheaf (subset hX n)).ι ≫ hom f)
    (range_le_of_isEtaleMorphism hX hY hf n))

theorem etaleRestriction_comp (n : ℕ) :
    hom (etaleRestriction hX hY hf n) ≫ hom (inclusion hY n) =
      hom (inclusion hX n) ≫ hom f :=
  Subfunctor.lift_ι ((PointOpenSubspace.subfunctor X.presheaf (subset hX n)).ι ≫ hom f)
    (range_le_of_isEtaleMorphism hX hY hf n)

theorem etaleRestriction_ringPoints {L : Type u} [CommRing L] [Algebra K L] (n : ℕ)
    (y : RingPoints K (space hX n) L) :
    RingPoints.map (inclusion hY n) (RingPoints.map (etaleRestriction hX hY hf n) y) =
      RingPoints.map f (RingPoints.map (inclusion hX n) y) :=
  congrArg (fun φ => φ.app (Opposite.op (ringTest K L)) y) (etaleRestriction_comp hX hY hf n)

/-- The restriction of an étale morphism to dimension pieces is étale. -/
theorem etaleRestriction_isEtaleMorphism (n : ℕ) :
    IsEtaleMorphism (etaleRestriction hX hY hf n) := by
  intro U φ hφ
  have h1 : IsEtale (φ ≫ hom (inclusion hX n)) :=
    hφ.comp (PointOpenSubspace.isEtale_of_isOpenImmersion (inclusion_isOpenImmersion hX n))
  have h2 := hf U _ h1
  rw [Category.assoc, ← etaleRestriction_comp hX hY hf n, ← Category.assoc] at h2
  have _ : Mono (hom (inclusion hY n)) :=
    inferInstanceAs (Mono (PointOpenSubspace.subfunctor Y.presheaf (subset hY n)).ι)
  exact IsEtale.of_comp_mono _ (hom (inclusion hY n)) h2

end Field

end SmoothDimensionPieces

namespace EtaleAnalyticIso

/-! ### Transporting open partial homeomorphisms along open embeddings -/

section Lift

variable {A B A' B' : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace A'] [TopologicalSpace B'] {i : A → A'} {j : B → B'}
  (e : OpenPartialHomeomorph A B) (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)
  [Nonempty A'] [Nonempty B]

/-- An open partial homeomorphism transported along open embeddings of its
source and target spaces. -/
def liftBoth : OpenPartialHomeomorph A' B' :=
  ((e.lift_openEmbedding hi).symm.lift_openEmbedding hj).symm

theorem liftBoth_source : (liftBoth e hi hj).source = i '' e.source := rfl

theorem liftBoth_target : (liftBoth e hi hj).target = j '' e.target := rfl

theorem liftBoth_apply (a : A) : liftBoth e hi hj (i a) = j (e a) := by
  rw [liftBoth, OpenPartialHomeomorph.lift_openEmbedding_symm,
    OpenPartialHomeomorph.symm_symm, Function.comp_apply,
    OpenPartialHomeomorph.lift_openEmbedding_apply]

theorem liftBoth_symm_apply (b : B) : (liftBoth e hi hj).symm (j b) = i (e.symm b) := by
  rw [liftBoth, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.lift_openEmbedding_apply,
    OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply]

end Lift

/-! ### Charts of analytic manifolds -/

/-- A map analytic on a subset of an analytic manifold, read in two atlas charts,
is analytic on the corresponding coordinate domain. -/
theorem contDiffOn_chart_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E E' M N : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
    [TopologicalSpace N] [ChartedSpace E' N] [IsManifold 𝓘(𝕜, E') ω N]
    {g : M → N} {s : Set M} (hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') ω g s)
    {d : OpenPartialHomeomorph M E} (hd : d ∈ atlas E M)
    {d' : OpenPartialHomeomorph N E'} (hd' : d' ∈ atlas E' N) :
    ContDiffOn 𝕜 ω (d' ∘ g ∘ d.symm) (d.target ∩ d.symm ⁻¹' (s ∩ g ⁻¹' d'.source)) := by
  have hs : s ∩ d.source ∩ g ⁻¹' d'.source ⊆ d.source := fun x hx => hx.1.2
  have h2s : MapsTo g (s ∩ d.source ∩ g ⁻¹' d'.source) d'.source := fun x hx => hx.2
  have h := (contMDiffOn_iff_of_mem_maximalAtlas' (IsManifold.subset_maximalAtlas hd)
    (IsManifold.subset_maximalAtlas hd') hs h2s).1 (hg.mono fun x hx => hx.1.1)
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id] at h
  refine h.mono ?_
  rintro z ⟨hz, hzs, hzd'⟩
  exact ⟨d.symm z, ⟨⟨hzs, d.map_target hz⟩, hzd'⟩, d.right_inv hz⟩

/-! ### Analyticity of maps lifted from one dimension piece -/

variable {K : Type u} [NontriviallyNormedField K]

/-- A map of original point spaces that agrees, on the image of a subset of a
dimension-`n` piece, with an analytic map of the dimension-`n` pieces is
analytic there for the assembled atlases. Charts of other dimensions meet the
relevant coordinate domains in the empty set. -/
theorem analyticOn_of_piece (σ : AnalyticPointStructure K) (hσ : σ.IsAnalytic)
    (hK : IsHenselianValuedField K) {X Y : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX : SmoothOverBase X) (hY : SmoothOverBase Y)
    (hXqs : IsQuasiSeparated X) (hXls : IsLocallySeparated X)
    (hYqs : IsQuasiSeparated Y) (hYls : IsLocallySeparated Y) (n : ℕ)
    (g : RingPoints K (SmoothDimensionPieces.space hX n) K →
      RingPoints K (SmoothDimensionPieces.space hY n) K)
    (s : Set (RingPoints K (SmoothDimensionPieces.space hX n) K))
    (hg : letI := etaleChartTopology K (SmoothDimensionPieces.space hX n)
      letI := etaleChartTopology K (SmoothDimensionPieces.space hY n)
      letI := σ.chartedSpace n (SmoothDimensionPieces.space hX n)
        (SmoothDimensionPieces.space_isSmoothPureDimensional hX hXqs hXls n)
      letI := σ.chartedSpace n (SmoothDimensionPieces.space hY n)
        (SmoothDimensionPieces.space_isSmoothPureDimensional hY hYqs hYls n)
      ContMDiffOn 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω g s)
    (G : RingPoints K X K → RingPoints K Y K)
    (hG : ∀ a ∈ s, G (RingPoints.map (SmoothDimensionPieces.inclusion hX n) a) =
      RingPoints.map (SmoothDimensionPieces.inclusion hY n) (g a))
    (hGc : @ContinuousOn _ _ (etaleChartTopology K X) (etaleChartTopology K Y) G
      (RingPoints.map (SmoothDimensionPieces.inclusion hX n) '' s)) :
    (σ.dimensionAtlas hK hX hXqs hXls).AnalyticOn (σ.dimensionAtlas hK hY hYqs hYls) G
      (RingPoints.map (SmoothDimensionPieces.inclusion hX n) '' s) := by
  refine ⟨hGc, ?_⟩
  intro n₁ m₁ c hc c' hc'
  let _ := etaleChartTopology K X
  let _ := etaleChartTopology K Y
  let _ := etaleChartTopology K (SmoothDimensionPieces.space hX n₁)
  let _ := σ.chartedSpace n₁ (SmoothDimensionPieces.space hX n₁)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hX hXqs hXls n₁)
  let _ := etaleChartTopology K (SmoothDimensionPieces.space hY m₁)
  let _ := σ.chartedSpace m₁ (SmoothDimensionPieces.space hY m₁)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hY hYqs hYls m₁)
  obtain ⟨d, hd, rfl⟩ := hc
  obtain ⟨d', hd', rfl⟩ := hc'
  by_cases hn : n₁ = n
  swap
  · intro z hz
    exfalso
    obtain ⟨-, ⟨a, -, ha⟩, -⟩ := hz
    have ha' : RingPoints.map (SmoothDimensionPieces.inclusion hX n) a =
        RingPoints.map (SmoothDimensionPieces.inclusion hX n₁) (d.symm z) := ha
    apply hn
    rw [← SmoothDimensionPieces.fieldPointDimension_map_inclusion hX n₁ (d.symm z), ← ha',
      SmoothDimensionPieces.fieldPointDimension_map_inclusion]
  subst hn
  by_cases hm : m₁ = n₁
  swap
  · intro z hz
    exfalso
    obtain ⟨-, ⟨a, ha_s, ha⟩, hb⟩ := hz
    have ha' : RingPoints.map (SmoothDimensionPieces.inclusion hX n₁) a =
        RingPoints.map (SmoothDimensionPieces.inclusion hX n₁) (d.symm z) := ha
    have hb' : G (RingPoints.map (SmoothDimensionPieces.inclusion hX n₁) (d.symm z)) ∈
        RingPoints.map (SmoothDimensionPieces.inclusion hY m₁) '' d'.source := hb
    obtain ⟨b, -, hb''⟩ := hb'
    rw [← ha', hG a ha_s] at hb''
    apply hm
    rw [← SmoothDimensionPieces.fieldPointDimension_map_inclusion hY m₁ b, hb'',
      SmoothDimensionPieces.fieldPointDimension_map_inclusion]
  subst hm
  have := hσ m₁ (SmoothDimensionPieces.space hX m₁)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hX hXqs hXls m₁)
  have := hσ m₁ (SmoothDimensionPieces.space hY m₁)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hY hYqs hYls m₁)
  have H := contDiffOn_chart_comp hg hd hd'
  have key : ∀ z ∈ (AnalyticPointStructure.liftDimensionChart hK hX hXqs m₁ d).target ∩
      (AnalyticPointStructure.liftDimensionChart hK hX hXqs m₁ d).symm ⁻¹'
        (RingPoints.map (SmoothDimensionPieces.inclusion hX m₁) '' s ∩
          G ⁻¹' (AnalyticPointStructure.liftDimensionChart hK hY hYqs m₁ d').source),
      z ∈ d.target ∧ d.symm z ∈ s ∧
        G ((AnalyticPointStructure.liftDimensionChart hK hX hXqs m₁ d).symm z) =
          RingPoints.map (SmoothDimensionPieces.inclusion hY m₁) (g (d.symm z)) ∧
        g (d.symm z) ∈ d'.source := by
    intro z hz
    obtain ⟨hzt, ⟨a, ha_s, ha⟩, hb⟩ := hz
    have ha' : RingPoints.map (SmoothDimensionPieces.inclusion hX m₁) a =
        RingPoints.map (SmoothDimensionPieces.inclusion hX m₁) (d.symm z) := ha
    have hadz : a = d.symm z :=
      SmoothDimensionPieces.fieldPointInclusion_injective hX m₁ ha'
    subst hadz
    have hGz : G ((AnalyticPointStructure.liftDimensionChart hK hX hXqs m₁ d).symm z) =
        RingPoints.map (SmoothDimensionPieces.inclusion hY m₁) (g (d.symm z)) :=
      hG _ ha_s
    have hb' : G ((AnalyticPointStructure.liftDimensionChart hK hX hXqs m₁ d).symm z) ∈
        RingPoints.map (SmoothDimensionPieces.inclusion hY m₁) '' d'.source := hb
    rw [hGz] at hb'
    obtain ⟨b, hb_s, hbe⟩ := hb'
    have hbg : b = g (d.symm z) :=
      SmoothDimensionPieces.fieldPointInclusion_injective hY m₁ hbe
    subst hbg
    exact ⟨hzt, ha_s, hGz, hb_s⟩
  refine ContDiffOn.congr (H.mono fun z hz => ?_) fun z hz => ?_
  · obtain ⟨hzt, hzs, -, hzd⟩ := key z hz
    exact ⟨hzt, hzs, hzd⟩
  · obtain ⟨-, -, hGz, -⟩ := key z hz
    simp only [Function.comp_apply]
    rw [hGz]
    exact OpenPartialHomeomorph.lift_openEmbedding_apply d'
      (AnalyticPointStructure.dimensionPiece_isOpenEmbedding hK hY hYqs m₁)

/-- Local analytic inverse branches of an étale morphism at the points of one
dimension piece. -/
theorem exists_branch (σ : AnalyticPointStructure K) (hσ : σ.IsAdmissible)
    (hK : IsHenselianValuedField K) {X Y : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX : SmoothOverBase X) (hY : SmoothOverBase Y)
    (hXqs : IsQuasiSeparated X) (hXls : IsLocallySeparated X)
    (hYqs : IsQuasiSeparated Y) (hYls : IsLocallySeparated Y) (f : X ⟶ Y)
    (hf : IsEtaleMorphism f) (n : ℕ)
    (y : RingPoints K (SmoothDimensionPieces.space hX n) K) :
    letI := etaleChartTopology K X
    letI := etaleChartTopology K Y
    ∃ e : OpenPartialHomeomorph (RingPoints K X K) (RingPoints K Y K),
      RingPoints.map (SmoothDimensionPieces.inclusion hX n) y ∈ e.source ∧
        Set.EqOn e (RingPoints.map (A := K) f) e.source ∧
        (σ.dimensionAtlas hK hX hXqs hXls).AnalyticOn (σ.dimensionAtlas hK hY hYqs hYls)
          e e.source ∧
        (σ.dimensionAtlas hK hY hYqs hYls).AnalyticOn (σ.dimensionAtlas hK hX hXqs hXls)
          e.symm e.target := by
  let _ := etaleChartTopology K X
  let _ := etaleChartTopology K Y
  let _ := etaleChartTopology K (SmoothDimensionPieces.space hX n)
  let _ := etaleChartTopology K (SmoothDimensionPieces.space hY n)
  let _ := σ.chartedSpace n (SmoothDimensionPieces.space hX n)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hX hXqs hXls n)
  let _ := σ.chartedSpace n (SmoothDimensionPieces.space hY n)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hY hYqs hYls n)
  let fn := SmoothDimensionPieces.etaleRestriction hX hY hf n
  have hloc := hσ.2.2.1 n _ _
    (SmoothDimensionPieces.space_isSmoothPureDimensional hX hXqs hXls n)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hY hYqs hYls n) fn
    (SmoothDimensionPieces.etaleRestriction_isEtaleMorphism hX hY hf n)
  obtain ⟨Φ, hyΦ, hEq⟩ := hloc y
  have _ : Nonempty (RingPoints K (SmoothDimensionPieces.space hY n) K) :=
    ⟨RingPoints.map fn y⟩
  have _ : Nonempty (RingPoints K X K) :=
    ⟨RingPoints.map (SmoothDimensionPieces.inclusion hX n) y⟩
  have hiX := AnalyticPointStructure.dimensionPiece_isOpenEmbedding hK hX hXqs n
  have hiY := AnalyticPointStructure.dimensionPiece_isOpenEmbedding hK hY hYqs n
  let e := liftBoth Φ.toOpenPartialHomeomorph hiX hiY
  refine ⟨e, ⟨y, hyΦ, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [liftBoth_apply]
    change RingPoints.map (SmoothDimensionPieces.inclusion hY n) (Φ a) = _
    rw [← hEq ha]
    exact SmoothDimensionPieces.etaleRestriction_ringPoints hX hY hf n a
  · exact analyticOn_of_piece σ hσ.1 hK hX hY hXqs hXls hYqs hYls n Φ Φ.source
      Φ.contMDiffOn e (fun a _ => liftBoth_apply _ hiX hiY a) e.continuousOn
  · exact analyticOn_of_piece σ hσ.1 hK hY hX hYqs hYls hXqs hXls n Φ.symm Φ.target
      Φ.symm.contMDiffOn e.symm (fun b _ => liftBoth_symm_apply _ hiX hiY b)
      e.symm.continuousOn

end EtaleAnalyticIso

/-- Étale morphisms of actual smooth, quasi-separated, locally separated spaces
are local analytic isomorphisms for the assembled varying-dimension atlases. -/
theorem smoothSourceDimensionEtaleAnalyticIso :
    SmoothSourceDimensionEtaleAnalyticIsoStatement.{u} := by
  intro K _ hK σ hσ X Y hX hY hXqs hXls hYqs hYls f hf
  refine ⟨fun x => SmoothDimensionPieces.fieldPointDimension_map_of_isEtaleMorphism hX hY hf x,
    fun x => ?_⟩
  have h := EtaleAnalyticIso.exists_branch σ hσ hK hX hY hXqs hXls hYqs hYls f hf
    (SmoothDimensionPieces.fieldPointDimension hX x)
    (SmoothDimensionPieces.fieldPointFactor hX x)
  rw [SmoothDimensionPieces.fieldPointFactor_map] at h
  exact h

end Langlands.AlgebraicGeometry.AlgebraicSpace
