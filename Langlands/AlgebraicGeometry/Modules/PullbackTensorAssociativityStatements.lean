import Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace Langlands.Scheme.Modules

/-- Associativity for the fixed pullback comparison on the localized monoidal tensor. -/
def LocalizedPullbackTensorAssociativityStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M N P : Y.Modules),
    localizedPullbackTensorComparisonApp f (M ⊗ N) P ≫
        (localizedPullbackTensorComparisonApp f M N ▷ (Scheme.Modules.pullback f).obj P) ≫
        (α_ ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
          ((Scheme.Modules.pullback f).obj P)).hom =
      (Scheme.Modules.pullback f).map (α_ M N P).hom ≫
        localizedPullbackTensorComparisonApp f M (N ⊗ P) ≫
        ((Scheme.Modules.pullback f).obj M ◁ localizedPullbackTensorComparisonApp f N P)

/-- Associativity for the canonical pullback comparison on the explicit sheafified tensor. -/
def ExplicitPullbackTensorAssociativityStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M N P : Y.Modules),
    pullbackTensorComparisonApp f (tensorObj M N) P ≫
        tensorMap (pullbackTensorComparisonApp f M N) (𝟙 ((Scheme.Modules.pullback f).obj P)) ≫
        (tensorAssociator ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
          ((Scheme.Modules.pullback f).obj P)).hom =
      (Scheme.Modules.pullback f).map (tensorAssociator M N P).hom ≫
        pullbackTensorComparisonApp f M (tensorObj N P) ≫
        tensorMap (𝟙 ((Scheme.Modules.pullback f).obj M)) (pullbackTensorComparisonApp f N P)

/-- Associativity for the fixed pullback comparisons in both published tensor conventions. -/
def PullbackTensorAssociativityStatement : Prop :=
  LocalizedPullbackTensorAssociativityStatement.{u} ∧
    ExplicitPullbackTensorAssociativityStatement.{u}

end Langlands.Scheme.Modules
