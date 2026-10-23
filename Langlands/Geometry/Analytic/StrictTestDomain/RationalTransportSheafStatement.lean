import Langlands.Geometry.Analytic.StrictTestDomain.RationalTransportContinuity

/-! # Sheaf comparison targets for the finite rational transport site -/

universe u v w

namespace Langlands.Analytic.StrictTestDomain.RationalTransport

open CategoryTheory

/-- A transport presheaf is a sheaf exactly when its restriction to ordinary
rational inclusions is a sheaf, with arbitrary categorical coefficients. -/
def SheafCriterionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K)
    (A : Type v) [Category.{w} A] (Q : (RationalTransport K P)ᵒᵖ ⥤ A),
    Presheaf.IsSheaf (finiteTopology K P) Q ↔
      Presheaf.IsSheaf (RationalData.finiteRationalTopology K P) (inclusion.op ⋙ Q)

/-- The actual transport and ordinary quotient-algebra presheaves have
equivalent sheaf conditions; neither sheaf condition is asserted outright. -/
def AlgebraSheafCriterionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K),
    Presheaf.IsSheaf (finiteTopology K P) (algebraPresheaf (K := K) (P := P)) ↔
      Presheaf.IsSheaf (RationalData.finiteRationalTopology K P)
        (RationalData.rationalPresheaf K P)

/-- The general restriction criterion together with its actual-algebra specialization. -/
def SheafComparisonStatement : Prop :=
  SheafCriterionStatement.{u, v, w} ∧ AlgebraSheafCriterionStatement.{u}

end Langlands.Analytic.StrictTestDomain.RationalTransport
