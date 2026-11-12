import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryStatement
import Langlands.AlgebraicGeometry.Picard.DualSchemeBaseChange
import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFlatStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFinitePresentationStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeProperStatement
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Residue-field comparison and reduction of relative dual geometry -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- The fibre of the actual chosen dual is isomorphic over the residue field to
the chosen dual of the fibre abelian scheme. -/
noncomputable def dualSchemeResidueFieldIso {S : Scheme.{u}} (A : AbelianScheme S)
    (hA : HasDualScheme A) (s : S) :
    (Over.pullback (S.fromSpecResidueField s)).obj (dualScheme A hA) ≅
      dualScheme ((baseChange (S.fromSpecResidueField s)).obj A)
        (hasDualScheme_baseChange picardZeroUniversalBaseChange
          (S.fromSpecResidueField s) A hA) :=
  dualSchemeBaseChangeIso picardZeroUniversalBaseChange (S.fromSpecResidueField s)
    A hA (hasDualScheme_baseChange picardZeroUniversalBaseChange
      (S.fromSpecResidueField s) A hA)

/-- Field geometry supplies smoothness and geometric connectedness of every
residue-field fibre of the chosen dual, over an arbitrary base. -/
lemma dualScheme_fiberToSpecResidueField
    (field : FieldDualSchemeGeometryStatement.{u}) {S : Scheme.{u}}
    (A : AbelianScheme S) (hA : HasDualScheme A) (s : S) :
    Smooth ((dualScheme A hA).hom.fiberToSpecResidueField s) ∧
      GeometricallyConnected ((dualScheme A hA).hom.fiberToSpecResidueField s) := by
  let b := S.fromSpecResidueField s
  let hA' : HasDualScheme ((baseChange b).obj A) :=
    hasDualScheme_baseChange picardZeroUniversalBaseChange b A hA
  obtain ⟨smooth, -, connected⟩ := field (S.residueField s) ((baseChange b).obj A) hA'
  let e := dualSchemeResidueFieldIso A hA s
  have w : e.hom.left ≫ (dualScheme ((baseChange b).obj A) hA').hom =
      (dualScheme A hA).hom.fiberToSpecResidueField s :=
    Over.w e.hom
  rw [← w]
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Smooth.{u})
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso
    (P := @GeometricallyConnected.{u})
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso @Smooth e.hom.left _).mpr smooth,
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
      e.hom.left _).mpr connected⟩

/-- Field geometry and the three non-fibrewise relative inputs imply the exact
published relative geometry target for the same chosen parameter schemes. -/
lemma RelativeDualSchemeGeometryStatement.of_flat_finitePresentation_proper
    (field : FieldDualSchemeGeometryStatement.{u})
    (flat : RelativeDualSchemeFlatStatement.{u})
    (finitePresentation : RelativeDualSchemeFinitePresentationStatement.{u})
    (proper : RelativeDualSchemeProperStatement.{u}) :
    RelativeDualSchemeGeometryStatement.{u} := by
  intro S _ A hA
  have : Flat (dualScheme A hA).hom := flat S A hA
  have : LocallyOfFinitePresentation (dualScheme A hA).hom := finitePresentation S A hA
  refine ⟨Smooth.of_smooth_fiberToSpecResidueField _ fun s ↦
      (dualScheme_fiberToSpecResidueField field A hA s).1,
    proper S A hA, ?_⟩
  exact (GeometricallyConnected.iff_geometricallyConnected_fiber _).mpr fun s ↦
    (dualScheme_fiberToSpecResidueField field A hA s).2

end Langlands.AbelianScheme
