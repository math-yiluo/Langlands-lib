import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothMorphismCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange
import Langlands.AlgebraicGeometry.SchemeEtalePureFibreDimension
import Langlands.AlgebraicGeometry.SchemePureFibreDimensionDescent
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.CategoryTheory.Filtered.Final

/-! # Pure fibre dimension of spaces along cofiltered affine limits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open SchemeFiberGeometry

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Pure fibre dimension of spaces holds on every commuting etale chart square.
The tested source chart need not be surjective. -/
theorem HasPureFibreDimension.pure_dimension_chart {d : ℕ} {f : X ⟶ Y}
    (hf : HasPureFibreDimension d f)
    {U V : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V)
    (ha : IsEtale a) (hb : IsEtale b)
    (hw : a ≫ hom f = (schemeYoneda S).map φ ≫ b) :
    PureFibreDimensionMorphismProperty d φ.left := by
  obtain ⟨A, B, x, y, ψ, hx, hs, hy, hψl, hψp, hcomm⟩ := hf
  let c : EtaleMorphismChart f := ⟨A, B, x, y, ψ, hx, hy, hcomm⟩
  let e : EtaleMorphismChart f := ⟨U, V, a, b, φ, ha, hb, hw⟩
  exact c.property_of_chart e (PureFibreDimensionMorphismProperty d)
    (pureFibreDimension_precomp_etale d)
    (pureFibreDimension_postcomp_etale d)
    (pureFibreDimension_of_postcomp_etale d)
    (pureFibreDimension_of_precomp_etale_surjective d)
    hs ⟨hψl, hψp⟩

/-- A commuting etale chart with surjective source tests the unchanged
algebraic-space pure-fibre-dimension definition exactly. -/
theorem hasPureFibreDimension_iff_chart {d : ℕ} {f : X ⟶ Y}
    {U V : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V)
    (ha : IsEtale a) (hs : IsSurjective a) (hb : IsEtale b)
    (hw : a ≫ hom f = (schemeYoneda S).map φ ≫ b) :
    HasPureFibreDimension d f ↔ PureFibreDimensionMorphismProperty d φ.left :=
  ⟨fun hf => hf.pure_dimension_chart a b φ ha hb hw,
    fun hφ => ⟨U, V, a, b, φ, ha, hs, hb, hφ.1, hφ.2, hw⟩⟩

/-- Pure fibre dimension of spaces is preserved by arbitrary scheme base change. -/
theorem HasPureFibreDimension.baseChangeMap {d : ℕ} {f : X ⟶ Y}
    (hf : HasPureFibreDimension d f) {T : Scheme.{u}} (g : T ⟶ S) :
    HasPureFibreDimension d (baseChangeMap g f) := by
  obtain ⟨U, V, a, b, φ, ha, hs, hb, hφl, hφp, hw⟩ := hf
  have hφ : PureFibreDimensionMorphismProperty d ((Over.pullback g).map φ).left :=
    schemeProperty_overPullback_map g (PureFibreDimensionMorphismProperty d) φ ⟨hφl, hφp⟩
  exact ⟨_, _, restrictAtlas g a, restrictAtlas g b, (Over.pullback g).map φ,
    relative_restrictAtlas _ ha, relative_restrictAtlas _ hs, relative_restrictAtlas _ hb,
    hφ.1, hφ.2, restrictAtlas_square g a b φ (hom f) hw⟩

variable {T : Scheme.{u}} (g : T ⟶ S)

private theorem overPullback_map_property_iff (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {U V : Over S} (φ : U ⟶ V) :
    P ((Over.pullback g).map φ).left ↔
      P (AffineLimit.baseChangeMap U.hom V.hom φ.left (Over.w φ) g) := by
  apply MorphismProperty.arrow_mk_iso_iff P
    (Arrow.isoMk (pullbackSymmetry U.hom g) (pullbackSymmetry V.hom g) ?_)
  change (pullbackSymmetry U.hom g).hom ≫
      AffineLimit.baseChangeMap U.hom V.hom φ.left (Over.w φ) g =
    ((Over.pullback g).map φ).left ≫ (pullbackSymmetry V.hom g).hom
  apply pullback.hom_ext <;>
    simp [Over.pullback_map_left, AffineLimit.baseChangeMap, Category.assoc]

private theorem pureFibreDimension_baseChangeMap_iff_chart
    (d : ℕ) {f : X ⟶ Y}
    {U V : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V)
    (ha : IsEtale a) (hs : IsSurjective a) (hb : IsEtale b)
    (hw : a ≫ hom f = (schemeYoneda S).map φ ≫ b) :
    HasPureFibreDimension d (baseChangeMap g f) ↔
      PureFibreDimensionMorphismProperty d
        (AffineLimit.baseChangeMap U.hom V.hom φ.left (Over.w φ) g) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (hasPureFibreDimension_iff_chart (f := baseChangeMap g f)
    (restrictAtlas g a) (restrictAtlas g b) ((Over.pullback g).map φ)
    (relative_restrictAtlas (g := g) _ ha) (relative_restrictAtlas (g := g) _ hs)
    (relative_restrictAtlas (g := g) _ hb)
    (restrictAtlas_square g a b φ (hom f) hw)).trans
    (overPullback_map_property_iff g (PureFibreDimensionMorphismProperty d) φ)

/-- Pure fibre dimension alone descends under the unchanged hypotheses on spaces. -/
def SpaceLimitPureFibreDimensionDescentStatement : Prop :=
  ∀ d : ℕ, SpaceLimitPropertyDescends.{u} (fun f => HasPureFibreDimension d f)

/-- Fixed affine charts reduce pure fibre dimension descent for spaces to the
relative scheme theorem, retaining arbitrary cofiltered indexing categories. -/
theorem spaceLimitPureFibreDimensionDescends :
    SpaceLimitPureFibreDimensionDescentStatement.{u} := by
  intro d I _ _ D _ c hc i X Y _ hX hYqs hY f
  obtain ⟨U, V, a, b, φ, hUa, hVa, ha, hs, hb, _, hUl, hVl, hw⟩ :=
    exists_affine_finitePresentation_chart_square hX hY hYqs f
  have : IsAffine U.left := hUa
  have : IsAffine V.left := hVa
  have : LocallyOfFinitePresentation V.hom := hVl
  have : LocallyOfFinitePresentation (φ.left ≫ V.hom) := by
    rw [Over.w φ]
    exact hUl
  have : LocallyOfFinitePresentation φ.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp φ.left V.hom
  let E : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D
  have (j : Over i) : IsAffine (E.obj j) := inferInstanceAs (IsAffine (D.obj j.left))
  let t : E ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app := fun j => D.map j.hom
      naturality := by
        intro j k r
        dsimp [E]
        rw [Category.comp_id, ← D.map_comp, Over.w r] }
  let cc : Cone E := c.whisker (Over.forget i)
  have hcc : IsLimit cc :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have hcomp (j : Over i) : cc.π.app j ≫ t.app j = c.π.app i := c.w j.hom
  have hd := SchemeLimitModel.relativePureFibreDimensionDescent d (Over i) E
    (D.obj i) U.left V.left t U.hom V.hom φ.left (Over.w φ) cc hcc (c.π.app i) hcomp
  have hP {B : Scheme.{u}} (q : B ⟶ D.obj i) :
      PureFibreDimensionMorphismProperty d
          (AffineLimit.baseChangeMap U.hom V.hom φ.left (Over.w φ) q) ↔
        HasPureDimensionFibers d
          (AffineLimit.baseChangeMap U.hom V.hom φ.left (Over.w φ) q) := by
    have hl : LocallyOfFiniteType
        (AffineLimit.baseChangeMap U.hom V.hom φ.left (Over.w φ) q) :=
      MorphismProperty.of_isPullback
        (SchemeLimitModel.Geometry.baseChangeMap_cartesian U.hom V.hom φ.left (Over.w φ) q).flip
        (inferInstanceAs (LocallyOfFiniteType φ.left))
    exact ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩
  refine (pureFibreDimension_baseChangeMap_iff_chart (c.π.app i) d a b φ ha hs hb hw).trans
    ((hP (c.π.app i)).trans (hd.trans ?_))
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j.left, j.hom,
      (pureFibreDimension_baseChangeMap_iff_chart (D.map j.hom) d a b φ ha hs hb hw).mpr
        ((hP (D.map j.hom)).mpr hj)⟩
  · rintro ⟨j, r, hj⟩
    exact ⟨Over.mk r, (hP (D.map r)).mp
      ((pureFibreDimension_baseChangeMap_iff_chart (D.map r) d a b φ ha hs hb hw).mp hj)⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
