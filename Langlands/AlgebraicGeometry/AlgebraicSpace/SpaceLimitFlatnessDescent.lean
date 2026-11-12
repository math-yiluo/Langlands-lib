import Langlands.AlgebraicGeometry.AlgebraicSpace.FlatMorphismCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange
import Langlands.AlgebraicGeometry.SchemeLimitRelativePropertyProof
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.CategoryTheory.Filtered.Final

/-! # Descent of flatness for algebraic spaces along affine limits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} (g : T ⟶ S)

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

private theorem isFlatMorphism_baseChangeMap_iff_chart
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {U V : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V)
    (ha : IsEtale a) (hs : IsSurjective a) (hb : IsEtale b)
    (hw : a ≫ hom f = (schemeYoneda S).map φ ≫ b) :
    IsFlatMorphism (baseChangeMap g f) ↔
      Flat (AffineLimit.baseChangeMap U.hom V.hom φ.left (Over.w φ) g) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (isFlatMorphism_iff_flat_chart (f := baseChangeMap g f) (restrictAtlas g a) (restrictAtlas g b)
    ((Over.pullback g).map φ) (relative_restrictAtlas (g := g) _ ha)
    (relative_restrictAtlas (g := g) _ hs) (relative_restrictAtlas (g := g) _ hb)
    (restrictAtlas_square g a b φ (hom f) hw)).trans
    (overPullback_map_property_iff g @Flat φ)

/-- Flatness descends along cofiltered affine limits under the unchanged
finite-presentation-atlas hypotheses of `SpaceLimitPropertyDescends`. -/
def SpaceLimitFlatnessDescentStatement : Prop :=
  SpaceLimitPropertyDescends.{u} (fun f => IsFlatMorphism f)

/-- Flatness of finitely presented algebraic spaces descends along any cofiltered
limit of affine schemes, with the original chart-based definition. -/
theorem spaceLimitFlatnessDescends :
    SpaceLimitFlatnessDescentStatement.{u} := by
  intro I _ _ D _ c hc i X Y _ hX hYqs hY f
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
  have hd := AffineLimit.relativeFlatDescent E t U.hom V.hom φ.left (Over.w φ)
    cc hcc (c.π.app i) hcomp
  refine (isFlatMorphism_baseChangeMap_iff_chart (c.π.app i) a b φ ha hs hb hw).trans
    (hd.trans ?_)
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j.left, j.hom,
      (isFlatMorphism_baseChangeMap_iff_chart (D.map j.hom) a b φ ha hs hb hw).mpr hj⟩
  · rintro ⟨j, r, hj⟩
    exact ⟨Over.mk r,
      (isFlatMorphism_baseChangeMap_iff_chart (D.map r) a b φ ha hs hb hw).mp hj⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
