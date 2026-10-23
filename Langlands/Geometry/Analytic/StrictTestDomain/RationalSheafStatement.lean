import Langlands.Geometry.Analytic.StrictTestDomain.RationalPresheaf

/-! # Finite rational descent for the actual quotient-algebra presheaf -/

universe u

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory
open RationalData

/-- Compatible sections on a finite point-covering family of actual rational
quotients have a unique section on the target quotient. -/
def FiniteRationalGluingStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (d : RationalData K P)
    (I : Type u) [Finite I] (D : I → RationalData K P) (f : ∀ i, D i ⟶ d),
    FamilyCovers d D →
    ∀ s : ∀ i, (D i).algebra,
      (∀ i j, (interLeft (D i) (D j)).restriction (s i) =
        (interRight (D i) (D j)).restriction (s j)) →
      ∃! a : d.algebra, ∀ i, (f i).restriction a = s i

/-- The constructed commutative K-algebra presheaf is a sheaf for the finite
rational covering topology over every presented strict affinoid. -/
def RationalPresheafSheafStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K),
    Presheaf.IsSheaf (finiteRationalTopology K P) (rationalPresheaf K P)

/-- The concrete finite section-gluing assertion and categorical sheaf assertion. -/
def RationalSheafStatement : Prop :=
  FiniteRationalGluingStatement.{u} ∧ RationalPresheafSheafStatement.{u}

end Langlands.Analytic.StrictTestDomain
