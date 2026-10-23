import Langlands.AlgebraicGeometry.Modules.TensorMonoidal
import Langlands.AlgebraicGeometry.Modules.PullbackTensor
import Langlands.AlgebraicGeometry.Modules.PullbackUnit

noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The associator on the explicit sheafified tensor, transported from monoidal localization. -/
def tensorAssociator (M N P : X.Modules) :
    tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) :=
  (localizedTensorIso X (tensorObj M N) P).symm ≪≫
    tensorIso (localizedTensorIso X M N).symm (Iso.refl P) ≪≫
      (α_ M N P) ≪≫
        tensorIso (Iso.refl M) (localizedTensorIso X N P) ≪≫
          localizedTensorIso X M (tensorObj N P)

/-- The fixed canonical pullback comparison, expressed for the localized monoidal tensors. -/
def localizedPullbackTensorComparison (f : X ⟶ Y) :
    tensor Y.Modules ⋙ Scheme.Modules.pullback f ⟶
      (Scheme.Modules.pullback f).prod (Scheme.Modules.pullback f) ⋙ tensor X.Modules :=
  CategoryTheory.Functor.whiskerRight (localizedTensorNatIso Y).hom (Scheme.Modules.pullback f) ≫
    pullbackTensorComparison f ≫
      CategoryTheory.Functor.whiskerLeft ((Scheme.Modules.pullback f).prod (Scheme.Modules.pullback f))
        (localizedTensorNatIso X).inv

/-- Component of the canonical pullback comparison on the localized tensor. -/
abbrev localizedPullbackTensorComparisonApp (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (M ⊗ N) ⟶
      (Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj N :=
  (localizedPullbackTensorComparison f).app (M, N)

/-- The localized comparison is conjugation of the explicit canonical comparison. -/
lemma localizedPullbackTensorComparisonApp_eq (f : X ⟶ Y) (M N : Y.Modules) :
    localizedPullbackTensorComparisonApp f M N =
      (Scheme.Modules.pullback f).map (localizedTensorIso Y M N).hom ≫
        pullbackTensorComparisonApp f M N ≫
          (localizedTensorIso X ((Scheme.Modules.pullback f).obj M)
            ((Scheme.Modules.pullback f).obj N)).inv :=
  rfl

end Langlands.Scheme.Modules
