import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothMorphismCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeMorphismComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AlgebraicGeometry.SchemeLimitRelativePropertyProof
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.CategoryTheory.Filtered.Final

/-! # Smooth limit descent from a fixed finitely presented chart square -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

namespace EtaleMorphismChart

/-- The actual scheme base changes form a chart square for the base-changed map. -/
def baseChange (c : EtaleMorphismChart f) (g : T ⟶ S) :
    EtaleMorphismChart (baseChangeMap g f) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨(Over.pullback g).obj c.source, (Over.pullback g).obj c.target,
    restrictAtlas g c.sourceMap, restrictAtlas g c.targetMap, (Over.pullback g).map c.schemeMap,
    relative_restrictAtlas _ c.sourceEtale, relative_restrictAtlas _ c.targetEtale,
    restrictAtlas_square g c.sourceMap c.targetMap c.schemeMap (hom f) c.comm⟩

/-- Changing the order of factors compares the slice base-change scheme map with
the convention used by the published scheme limit theorem. -/
def schemeBaseChangeArrowIso (c : EtaleMorphismChart f) (g : T ⟶ S) :
    Arrow.mk ((Over.pullback g).map c.schemeMap).left ≅
      Arrow.mk (AffineLimit.baseChangeMap c.source.hom c.target.hom
        c.schemeMap.left (Over.w c.schemeMap) g) :=
  Arrow.isoMk (pullbackSymmetry c.source.hom g) (pullbackSymmetry c.target.hom g) (by
    apply pullback.hom_ext <;>
      simp only [Arrow.mk_hom, AffineLimit.baseChangeMap, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_snd_assoc])

/-- Smoothness of a space map after base change is tested by the base change of
any fixed étale square with surjective source. -/
theorem smooth_baseChange_iff (c : EtaleMorphismChart f) (hs : IsSurjective c.sourceMap)
    (g : T ⟶ S) :
    IsSmoothMorphism (baseChangeMap g f) ↔
      Smooth (AffineLimit.baseChangeMap c.source.hom c.target.hom
        c.schemeMap.left (Over.w c.schemeMap) g) := by
  have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let d := c.baseChange g
  have hsd : IsSurjective d.sourceMap := relative_restrictAtlas _ hs
  exact (isSmoothMorphism_iff_smooth_chart d.sourceMap d.targetMap d.schemeMap
    d.sourceEtale hsd d.targetEtale d.comm).trans
      (MorphismProperty.arrow_mk_iso_iff @Smooth (c.schemeBaseChangeArrowIso g))

end EtaleMorphismChart

/-- Given a fixed chart square with the scheme finiteness required by relative
smooth descent, smoothness at an affine limit is detected at a later stage.
The existence of such a chart square is a separate geometric obligation. -/
theorem smooth_baseChangeMap_iff_exists_stage_of_chart
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (i : I) {X Y : AlgebraicSpace (D.obj i)} (f : X ⟶ Y)
    (a : EtaleMorphismChart f) (hs : IsSurjective a.sourceMap)
    [LocallyOfFinitePresentation a.schemeMap.left] [QuasiCompact a.schemeMap.left]
    [QuasiSeparated a.schemeMap.left] [QuasiCompact a.target.hom] :
    IsSmoothMorphism (baseChangeMap (c.π.app i) f) ↔
      ∃ (j : I) (r : j ⟶ i), IsSmoothMorphism (baseChangeMap (D.map r) f) := by
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
  have hdesc := AffineLimit.relativeSmoothDescent E t a.source.hom a.target.hom
    a.schemeMap.left (Over.w a.schemeMap) c' hc' (c.π.app i) (fun j => c.w j.hom)
  constructor
  · intro hf
    obtain ⟨j, hj⟩ := hdesc.mp ((a.smooth_baseChange_iff hs (c.π.app i)).mp hf)
    exact ⟨j.left, j.hom, (a.smooth_baseChange_iff hs (D.map j.hom)).mpr hj⟩
  · rintro ⟨j, r, hr⟩
    exact isSmoothMorphism_baseChangeMap_of_stage D c r f hr

/-- The smoothness conjunct of the eight-property limit-descent statement,
using a fixed affine finite-presentation chart at the original stage. -/
theorem spaceLimitSmoothDescent :
    SpaceLimitPropertyDescends.{u} (fun f => IsSmoothMorphism f) := by
  intro I _ _ D _ c hc i X Y _ hX hYqs hY f
  obtain ⟨W, V, a, b, φ, hWa, hVa, ha, hs, hb, _, hWl, hVl, hw⟩ :=
    exists_affine_finitePresentation_chart_square hX hY hYqs f
  let : IsAffine W.left := hWa
  let : IsAffine V.left := hVa
  let : LocallyOfFinitePresentation W.hom := hWl
  let : LocallyOfFinitePresentation V.hom := hVl
  have : LocallyOfFinitePresentation (φ.left ≫ V.hom) := by
    rw [Over.w φ]
    exact hWl
  let : LocallyOfFinitePresentation φ.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp φ.left V.hom
  let chart : EtaleMorphismChart f := ⟨W, V, a, b, φ, ha, hb, hw⟩
  exact smooth_baseChangeMap_iff_exists_stage_of_chart D c hc i f chart hs

end Langlands.AlgebraicGeometry.AlgebraicSpace
