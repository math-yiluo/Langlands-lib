import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerReduction
import Langlands.AlgebraicGeometry.Picard.MumfordDualDirectImages
import Langlands.AlgebraicGeometry.Picard.FiniteFlatPointFibreSections

/-! # The dual-side Euler characteristic from its prerequisite statements -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The Poincaré direct images, flat base change, the higher projection formula and the
geometry of the dual over a field together imply the dual-side Euler characteristic of a
finite flat Mumford map. -/
def AlgClosedFieldMumfordDualEulerReductionStatement : Prop :=
  AlgClosedFieldPoincareDirectImageStatement.{u} →
    FlatHigherDirectImageBaseChangeStatement.{u} →
    LineBundleHigherProjectionFormulaStatement.{u} →
    FieldDualSchemeGeometryStatement.{u} →
    AlgClosedFieldMumfordDualEulerStatement.{u}

/-- The reduction holds. -/
theorem algClosedFieldMumfordDualEulerReduction :
    AlgClosedFieldMumfordDualEulerReductionStatement.{u} := by
  intro poincare flat projection hgeom preservation square K _ _ A hA L B evaluationB M
    evaluation f hf _ hflat g hg hQ y
  obtain ⟨hzero, ⟨iso⟩⟩ := mumfordDual_higherDirectImage preservation K A hA L B evaluationB
    M evaluation square poincare flat projection f hf hflat g hg
  let N := (RigidifiedLineBundle.forget (unitSection A)).obj
    (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A) L B
      evaluationB)
  have he : (dualOrigin A hA).left ≫ (dualScheme A hA).hom = 𝟙 _ := Over.w (dualOrigin A hA)
  have hfD : f.left ≫ (dualScheme A hA).hom = A.X.hom := Over.w f
  have hsupp := (hasFiniteClosedSupport_iff_of_iso iso).2
    (FiniteFlatPointFibre.hasFiniteClosedSupport_tensor_pullback_pushforward flat
      (dualScheme A hA).hom f.left (dualOrigin A hA).left he N)
  refine (eulerCharacteristic_comp_eq_of_concentrated (pullback.fst A.X.hom A.X.hom) A.X.hom
    _ g hzero hsupp hQ).trans ?_
  congr 2
  refine ((relativeGlobalSections A.X.hom).mapIso iso).toLinearEquiv.finrank_eq.trans
    ((FiniteFlatPointFibre.finrank_relativeGlobalSections_tensor_pullback_pushforward flat
      A.X.hom (dualScheme A hA).hom f.left hfD (dualOrigin A hA).left he N
      ((dualScheme A hA).hom y)).trans ?_)
  exact finrank_eq_of_fieldDualSchemeGeometry hgeom K A hA f _ y

end Langlands.AbelianScheme
