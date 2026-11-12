import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeDiagonalCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeMorphismComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AlgebraicGeometry.SchemeLimitRelativeClosedImmersionProof
import Mathlib.CategoryTheory.Filtered.Final

/-! # Separatedness descent from a fixed relative-diagonal chart -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A relative property is tested on any represented pullback along a surjective
étale atlas, with representability of the map retained as a premise. -/
theorem relativeProperty_iff_of_etale_atlas
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u})]
    {F G : Presheaf S} {f : F ⟶ G} (hr : IsRepresentableMorphism f)
    {R U : Over S} (a : (schemeYoneda S).obj U ⟶ G)
    (ha : IsEtale a) (hs : IsSurjective a)
    (b : (schemeYoneda S).obj R ⟶ F) (q : R ⟶ U)
    (h : IsPullback b ((schemeYoneda S).map q) f a) :
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) f ↔
      P q.left := by
  constructor
  · intro hf
    exact hf.2 a b q h
  · intro hq
    have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hc : P (hr.snd a).left := by
      let e := (schemeYoneda S).preimageIso
        ((hr.isPullback a).isoIsPullback _ _ h)
      have he : e.hom ≫ q = hr.snd a := by
        apply (schemeYoneda S).map_injective
        simp [e, Functor.map_comp]
      have : IsIso e.hom.left := by
        change IsIso ((Over.forget S).map e.hom)
        infer_instance
      rw [← he]
      exact (P.cancel_left_of_respectsIso _ _).mpr hq
    exact relativeProperty_of_etale_atlas P hr a ha hs hc

/-- The slice pullback convention and the scheme limit convention differ only
by exchanging their two factors. -/
def overPullbackSchemeArrowIso {R U : Over S} (q : R ⟶ U) (g : T ⟶ S) :
    Arrow.mk ((Over.pullback g).map q).left ≅
      Arrow.mk (AffineLimit.baseChangeMap R.hom U.hom q.left (Over.w q) g) :=
  Arrow.isoMk (pullbackSymmetry R.hom g) (pullbackSymmetry U.hom g) (by
    apply pullback.hom_ext <;>
      simp only [Arrow.mk_hom, AffineLimit.baseChangeMap, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_snd_assoc])

namespace RelativeDiagonalChart

variable (f : X ⟶ Y) {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)

/-- The actual base change of the original target chart, with the canonical
comparison from restriction of a pullback to the pullback of the restrictions. -/
def baseChangeAtlas (g : T ⟶ S) :
    (schemeYoneda T).obj ((Over.pullback g).obj (target f a)) ⟶
      Limits.pullback (hom (baseChangeMap g f)) (hom (baseChangeMap g f)) :=
  restrictAtlas g (atlas f a) ≫ (restrictPresheafPullbackIso g (hom f) (hom f)).hom

/-- The original scheme comparison remains a represented relative-diagonal
square after an arbitrary scheme base change. -/
theorem baseChange_comparison_isPullback (g : T ⟶ S) :
    IsPullback (restrictAtlas g ((schemeYoneda S).map (sourceFst a) ≫ a))
      ((schemeYoneda T).map ((Over.pullback g).map (comparison f a)))
      (pullback.diagonal (hom (baseChangeMap g f))) (baseChangeAtlas f a g) := by
  apply ((comparison_isPullback f a).map (restrictPresheaf g)).of_iso'
    (schemeYonedaBaseChangeIso g (source a)) (Iso.refl _)
    (schemeYonedaBaseChangeIso g (target f a))
    (restrictPresheafPullbackIso g (hom f) (hom f)).symm
  · simp only [Iso.refl_hom, Category.comp_id, restrictAtlas]
  · exact ((schemeYonedaBaseChangeNatIso g).hom.naturality (comparison f a)).symm
  · change (𝟙 _) ≫ (restrictPresheaf g).map (pullback.diagonal (hom f)) =
      pullback.diagonal ((restrictPresheaf g).map (hom f)) ≫
        (restrictPresheafPullbackIso g (hom f) (hom f)).inv
    rw [← restrictPresheaf_map_pullback_diagonal]
    simp
  · simp [baseChangeAtlas, restrictAtlas]

theorem baseChangeAtlas_isEtale (ha : IsEtale a) (g : T ⟶ S) :
    IsEtale (baseChangeAtlas f a g) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have ht : IsEtale (restrictAtlas g (atlas f a)) :=
    relative_restrictAtlas _ (atlas_isEtale f a ha)
  exact ht.comp_iso
    (restrictPresheafPullbackIso g (hom f) (hom f))

theorem baseChangeAtlas_isSurjective (hs : IsSurjective a) (g : T ⟶ S) :
    IsSurjective (baseChangeAtlas f a g) := by
  change IsSurjective (restrictAtlas g (atlas f a) ≫
    (restrictPresheafPullbackIso g (hom f) (hom f)).hom)
  apply (MorphismProperty.cancel_right_of_respectsIso
    ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget T)).relative
      (schemeYoneda T)) _ _).mpr
  exact relative_restrictAtlas _ (atlas_isSurjective f a hs)

/-- Separatedness after base change is tested by the same base change of one
fixed scheme comparison at the original stage. -/
theorem separated_baseChange_iff (ha : IsEtale a) (hs : IsSurjective a) (g : T ⟶ S) :
    IsSeparatedMorphism (baseChangeMap g f) ↔
      _root_.AlgebraicGeometry.IsClosedImmersion
        (AffineLimit.baseChangeMap (source a).hom (target f a).hom
          (comparison f a).left (Over.w (comparison f a)) g) := by
  exact (relativeProperty_iff_of_etale_atlas @_root_.AlgebraicGeometry.IsClosedImmersion
    (relative_diagonal_representable (baseChangeMap g f)) (baseChangeAtlas f a g)
    (baseChangeAtlas_isEtale f a ha g) (baseChangeAtlas_isSurjective f a hs g)
    _ _ (baseChange_comparison_isPullback f a g)).trans
      (MorphismProperty.arrow_mk_iso_iff @_root_.AlgebraicGeometry.IsClosedImmersion
        (overPullbackSchemeArrowIso (comparison f a) g))

/-- A scheme kernel pair of an affine chart is separated over an affine base:
its pairing into the product of the chart with itself is a monomorphism. -/
theorem source_isSeparated [IsAffine S] [IsAffine U.left] :
    _root_.AlgebraicGeometry.IsSeparated (source a).hom := by
  let j : source a ⟶ U ⨯ U := prod.lift (sourceFst a) (sourceSnd a)
  have : Mono j := by
    constructor
    intro Z g h e
    apply Functor.relativelyRepresentable.hom_ext' (X.representable_from_scheme a)
    · simpa [j] using congrArg (fun k => k ≫ prod.fst) e
    · simpa [j] using congrArg (fun k => k ≫ prod.snd) e
  have : IsAffine (U ⨯ U).left :=
    IsAffine.of_isIso (Over.prodLeftIsoPullback U U).hom
  have : _root_.AlgebraicGeometry.IsSeparated (U ⨯ U).hom := inferInstance
  rw [← Over.w j]
  infer_instance

/-- The kernel pair of a chart into a quasi-separated space is compact when
the chart scheme is affine. -/
theorem source_compactSpace [IsAffine S] [IsAffine U.left] (hX : IsQuasiSeparated X) :
    CompactSpace (source a).left := by
  have : IsAffine (U ⨯ U).left :=
    IsAffine.of_isIso (Over.prodLeftIsoPullback U U).hom
  have : QuasiCompact (prod.lift (sourceFst a) (sourceSnd a)).left :=
    relative_diagonal_property_chart_pairing @QuasiCompact hX
      (sourceFst a) (sourceSnd a) a a (source_isPullback a)
  exact QuasiCompact.compactSpace_of_compactSpace
    (prod.lift (sourceFst a) (sourceSnd a)).left

/-- The relation scheme of an étale chart locally of finite presentation over
the base is locally of finite presentation over the base. -/
theorem source_locallyOfFinitePresentation (ha : IsEtale a)
    [LocallyOfFinitePresentation U.hom] :
    LocallyOfFinitePresentation (source a).hom := by
  have : Etale (sourceSnd a).left :=
    ha.projection a _ _ (source_isPullback a)
  rw [← Over.w (sourceSnd a)]
  infer_instance

end RelativeDiagonalChart

/-- With the scheme finiteness hypotheses for one diagonal chart, separatedness
at the affine limit is equivalent to separatedness at a later stage. -/
theorem separated_baseChangeMap_iff_exists_stage_of_chart
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (i : I) {X Y : AlgebraicSpace (D.obj i)} (f : X ⟶ Y)
    {U : Over (D.obj i)} (a : (schemeYoneda (D.obj i)).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType (RelativeDiagonalChart.comparison f a).left]
    [QuasiCompact (RelativeDiagonalChart.comparison f a).left]
    [QuasiSeparated (RelativeDiagonalChart.comparison f a).left]
    [QuasiCompact (RelativeDiagonalChart.target f a).hom] :
    IsSeparatedMorphism (baseChangeMap (c.π.app i) f) ↔
      ∃ (j : I) (r : j ⟶ i), IsSeparatedMorphism (baseChangeMap (D.map r) f) := by
  let E := Over.forget i ⋙ D
  let t : E ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app := fun j => D.map j.hom
      naturality := by
        intro j k r
        change D.map r.left ≫ D.map k.hom = D.map j.hom ≫ 𝟙 _
        rw [← D.map_comp, Over.w r, Category.comp_id] }
  have (j : Over i) : IsAffine (E.obj j) := by dsimp [E]; infer_instance
  let c' := c.whisker (Over.forget i)
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have hdesc := AffineLimit.relativeClosedImmersionDescent E t
    (RelativeDiagonalChart.source a).hom (RelativeDiagonalChart.target f a).hom
    (RelativeDiagonalChart.comparison f a).left (Over.w (RelativeDiagonalChart.comparison f a))
    c' hc' (c.π.app i) (fun j => c.w j.hom)
  constructor
  · intro hf
    obtain ⟨j, hj⟩ := hdesc.mp
      ((RelativeDiagonalChart.separated_baseChange_iff f a ha hs (c.π.app i)).mp hf)
    exact ⟨j.left, j.hom,
      (RelativeDiagonalChart.separated_baseChange_iff f a ha hs (D.map j.hom)).mpr hj⟩
  · rintro ⟨j, r, hr⟩
    exact isSeparatedMorphism_baseChangeMap_of_stage D c r f hr

/-- The separatedness conjunct of the eight-property limit-descent statement. -/
theorem spaceLimitSeparatedDescent :
    SpaceLimitPropertyDescends.{u} (fun f => IsSeparatedMorphism f) := by
  intro I _ _ D _ c hc i X Y hXqs hX hYqs _ f
  obtain ⟨U, a, hUa, ha, hs, hUl⟩ := exists_affine_finitePresentation_atlas X hX
  let : IsAffine U.left := hUa
  let : LocallyOfFinitePresentation U.hom := hUl
  have : LocallyOfFinitePresentation (RelativeDiagonalChart.source a).hom :=
    RelativeDiagonalChart.source_locallyOfFinitePresentation a ha
  have : CompactSpace (RelativeDiagonalChart.source a).left :=
    RelativeDiagonalChart.source_compactSpace a hXqs
  have : CompactSpace (RelativeDiagonalChart.target f a).left :=
    RelativeDiagonalChart.source_compactSpace (a ≫ hom f) hYqs
  have : _root_.AlgebraicGeometry.IsSeparated (RelativeDiagonalChart.source a).hom :=
    RelativeDiagonalChart.source_isSeparated a
  have : _root_.AlgebraicGeometry.IsSeparated (RelativeDiagonalChart.target f a).hom :=
    RelativeDiagonalChart.source_isSeparated (a ≫ hom f)
  have : QuasiSeparatedSpace (RelativeDiagonalChart.target f a).left :=
    quasiSeparatedSpace_of_quasiSeparated (RelativeDiagonalChart.target f a).hom
  have : LocallyOfFiniteType ((RelativeDiagonalChart.comparison f a).left ≫
      (RelativeDiagonalChart.target f a).hom) := by
    rw [Over.w (RelativeDiagonalChart.comparison f a)]
    infer_instance
  have : LocallyOfFiniteType (RelativeDiagonalChart.comparison f a).left :=
    locallyOfFiniteType_of_comp _ (RelativeDiagonalChart.target f a).hom
  have : _root_.AlgebraicGeometry.IsSeparated ((RelativeDiagonalChart.comparison f a).left ≫
      (RelativeDiagonalChart.target f a).hom) := by
    rw [Over.w (RelativeDiagonalChart.comparison f a)]
    infer_instance
  have : _root_.AlgebraicGeometry.IsSeparated (RelativeDiagonalChart.comparison f a).left :=
    _root_.AlgebraicGeometry.IsSeparated.of_comp _ (RelativeDiagonalChart.target f a).hom
  exact separated_baseChangeMap_iff_exists_stage_of_chart D c hc i f a ha hs

end Langlands.AlgebraicGeometry.AlgebraicSpace
