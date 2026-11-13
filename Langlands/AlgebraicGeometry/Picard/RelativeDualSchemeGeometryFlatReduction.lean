import Langlands.AlgebraicGeometry.Picard.DualSchemeGeometryAssembly
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceProof

/-! # Relative dual geometry from field smoothness, flatness and local finite presentation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over an arbitrary base, field smoothness of chosen duals makes a flat chosen dual that is
locally of finite presentation smooth. -/
theorem dualScheme_smooth_of_flat_of_locallyOfFinitePresentation
    (fieldSmooth : FieldDualSchemeSmoothStatement.{u}) {S : Scheme.{u}}
    (A : AbelianScheme S) (hA : HasDualScheme A) [Flat (dualScheme A hA).hom]
    [LocallyOfFinitePresentation (dualScheme A hA).hom] :
    Smooth (dualScheme A hA).hom :=
  Smooth.of_smooth_fiberToSpecResidueField _ fun s =>
    (dualScheme_fiberToSpecResidueField
      (FieldDualSchemeGeometryStatement.of_smooth fieldSmooth) A hA s).1

/-- Field smoothness, relative flatness and relative local finite presentation of chosen duals
imply the relative geometry statement over every quasi-separated base. -/
def RelativeDualSchemeGeometryFlatReductionStatement : Prop :=
  FieldDualSchemeSmoothStatement.{u} → RelativeDualSchemeFlatStatement.{u} →
    RelativeDualSchemeFinitePresentationStatement.{u} → RelativeDualSchemeGeometryStatement.{u}

/-- The relative geometry statement follows from field smoothness, flatness and local finite
presentation; properness comes from the published valuative existence theorem. -/
theorem relativeDualSchemeGeometryFlatReduction :
    RelativeDualSchemeGeometryFlatReductionStatement.{u} := by
  intro fieldSmooth flat finitePresentation S _ A hA
  have : Flat (dualScheme A hA).hom := flat S A hA
  have : LocallyOfFinitePresentation (dualScheme A hA).hom := finitePresentation S A hA
  have : Smooth (dualScheme A hA).hom :=
    dualScheme_smooth_of_flat_of_locallyOfFinitePresentation fieldSmooth A hA
  exact dualSchemeGeometry_of_smooth relativeDualSchemeValuativeExistence A hA

end Langlands.AbelianScheme
