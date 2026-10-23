import Langlands.AlgebraicGeometry.Modules.TensorMonoidal

universe u

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry

namespace Langlands.Scheme.Modules

/-- The localized left unitor agrees with the explicit sheafified left unitor. -/
def TensorMonoidalLeftUnitorComparisonStatement : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules),
    (localizedTensorIso X (structureSheaf X) M).hom ≫ (tensorLeftUnitor M).hom =
      (λ_ M).hom

/-- The localized right unitor agrees with the explicit sheafified right unitor. -/
def TensorMonoidalRightUnitorComparisonStatement : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules),
    (localizedTensorIso X M (structureSheaf X)).hom ≫ (tensorRightUnitor M).hom =
      (ρ_ M).hom

/-- The localized braiding agrees with the explicit sheafified factor swap. -/
def TensorMonoidalSymmetryComparisonStatement : Prop :=
  ∀ (X : Scheme.{u}) (M N : X.Modules),
    (localizedTensorIso X M N).hom ≫ (tensorComm M N).hom =
      (β_ M N).hom ≫ (localizedTensorIso X N M).hom

/-- Agreement of localized unitors and symmetry with the fixed explicit tensor maps. -/
def TensorMonoidalComparisonStatement : Prop :=
  TensorMonoidalLeftUnitorComparisonStatement.{u} ∧
    TensorMonoidalRightUnitorComparisonStatement.{u} ∧
      TensorMonoidalSymmetryComparisonStatement.{u}

end Langlands.Scheme.Modules
