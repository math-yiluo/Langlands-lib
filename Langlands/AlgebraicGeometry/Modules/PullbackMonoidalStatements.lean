import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme.Modules

/-- The existing identity pullback comparison is monoidal for canonical pullback. -/
def PullbackIdentityMonoidalStatement : Prop :=
  ∀ X : Scheme.{u}, NatTrans.IsMonoidal (Scheme.Modules.pullbackId X).hom

/-- The existing composite pullback comparison is monoidal for canonical pullback. -/
def PullbackCompositionMonoidalStatement : Prop :=
  ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z),
    NatTrans.IsMonoidal (Scheme.Modules.pullbackComp f g).hom

/-- Monoidality of both fixed identity and composition pullback comparisons. -/
def PullbackComparisonsMonoidalStatement : Prop :=
  PullbackIdentityMonoidalStatement.{u} ∧ PullbackCompositionMonoidalStatement.{u}

end Langlands.Scheme.Modules
