import Langlands.AlgebraicGeometry.RelativeDifferentials

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

/-- Every relative derivation factors uniquely through the constructed
relative differential sheaf and its distinguished derivation. -/
def RelativeDifferentialsUniversalStatement {X S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) : Prop :=
  ∀ (M : X.Modules), Function.Bijective
    (fun (α : relativeDifferentials f ⟶ M) =>
      RelativeDerivation.postcomp (relativeDifferentialsDerivation f) α)

end Langlands.Scheme
