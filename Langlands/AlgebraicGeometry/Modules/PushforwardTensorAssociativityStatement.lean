import Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme.Modules

/-- Associativity of the canonical pushforward tensor map for the fixed explicit tensor. -/
def PushforwardTensorAssociativityStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M N P : X.Modules),
    tensorMap (pushforwardTensorApp f M N) (𝟙 ((Scheme.Modules.pushforward f).obj P)) ≫
        pushforwardTensorApp f (tensorObj M N) P ≫
        (Scheme.Modules.pushforward f).map (tensorAssociator M N P).hom =
      (tensorAssociator ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N) ((Scheme.Modules.pushforward f).obj P)).hom ≫
        tensorMap (𝟙 ((Scheme.Modules.pushforward f).obj M)) (pushforwardTensorApp f N P) ≫
        pushforwardTensorApp f M (tensorObj N P)

end Langlands.Scheme.Modules
