import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicHomComparisonStatement

/-! # Statements: diagonalizable adic Hom comparison and finite étale descent -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- The globally diagonalizable case of SGA 3, Exposé IX, Théorème 7.1. -/
def DiagonalizableAdicHomComparisonStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [IsAffineHom G.X.hom],
      IsDiagonalizable H →
        Function.Bijective (HomScheme.Adic.System.restrict I H G)

/-- The finite étale descent step of SGA 3, Exposé IX, Théorème 7.1. -/
def MultiplicativeTypeAdicHomDescentStatement : Prop :=
  DiagonalizableAdicHomComparisonStatement.{u} →
    MultiplicativeTypeAdicHomComparisonStatement.{u}

end Langlands.GroupScheme
