import Langlands.AlgebraicGeometry.Modules.PullbackTensor
import Langlands.AlgebraicGeometry.Modules.PullbackUnit

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Langlands.Scheme.Modules

/-- The canonical pullback comparisons respect the explicit left tensor unitor. -/
def PullbackTensorLeftUnitorStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : Y.Modules),
    pullbackTensorComparisonApp f (structureSheaf Y) M ≫
        tensorMap (pullbackUnitIso f).hom (𝟙 ((Scheme.Modules.pullback f).obj M)) ≫
        (tensorLeftUnitor ((Scheme.Modules.pullback f).obj M)).hom =
      (Scheme.Modules.pullback f).map (tensorLeftUnitor M).hom

/-- The canonical pullback comparisons respect the explicit right tensor unitor. -/
def PullbackTensorRightUnitorStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : Y.Modules),
    pullbackTensorComparisonApp f M (structureSheaf Y) ≫
        tensorMap (𝟙 ((Scheme.Modules.pullback f).obj M)) (pullbackUnitIso f).hom ≫
        (tensorRightUnitor ((Scheme.Modules.pullback f).obj M)).hom =
      (Scheme.Modules.pullback f).map (tensorRightUnitor M).hom

/-- Both tensor-unit compatibility laws for the canonical scheme-module pullback comparisons. -/
def PullbackTensorUnitCoherenceStatement : Prop :=
  PullbackTensorLeftUnitorStatement.{u} ∧ PullbackTensorRightUnitorStatement.{u}

end Langlands.Scheme.Modules
