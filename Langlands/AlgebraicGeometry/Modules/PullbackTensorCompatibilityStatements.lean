import Langlands.AlgebraicGeometry.Modules.PullbackTensor

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme.Modules

/-- The canonical tensor comparison respects the existing identity pullback isomorphism. -/
def PullbackTensorIdentityStatement : Prop :=
  ∀ (X : Scheme.{u}) (M N : X.Modules),
    pullbackTensorComparisonApp (𝟙 X) M N ≫
        tensorMap ((Scheme.Modules.pullbackId X).hom.app M)
          ((Scheme.Modules.pullbackId X).hom.app N) =
      (Scheme.Modules.pullbackId X).hom.app (tensorObj M N)

/-- The canonical tensor comparison respects the existing composite pullback isomorphism. -/
def PullbackTensorCompositionStatement : Prop :=
  ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules),
    (Scheme.Modules.pullbackComp f g).hom.app (tensorObj M N) ≫
        pullbackTensorComparisonApp (f ≫ g) M N =
      (Scheme.Modules.pullback f).map (pullbackTensorComparisonApp g M N) ≫
        pullbackTensorComparisonApp f ((Scheme.Modules.pullback g).obj M)
          ((Scheme.Modules.pullback g).obj N) ≫
        tensorMap ((Scheme.Modules.pullbackComp f g).hom.app M)
          ((Scheme.Modules.pullbackComp f g).hom.app N)

/-- The canonical tensor comparison commutes with the explicit swap of tensor factors. -/
def PullbackTensorSymmetryStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M N : Y.Modules),
    pullbackTensorComparisonApp f M N ≫
        (tensorComm ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N)).hom =
      (Scheme.Modules.pullback f).map (tensorComm M N).hom ≫
        pullbackTensorComparisonApp f N M

/-- Identity, composition, and explicit symmetry compatibility for the canonical tensor comparison. -/
def PullbackTensorCompatibilityStatement : Prop :=
  PullbackTensorIdentityStatement.{u} ∧
    PullbackTensorCompositionStatement.{u} ∧ PullbackTensorSymmetryStatement.{u}

end Langlands.Scheme.Modules
