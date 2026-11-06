import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRationalIdealDescentStatement
import Langlands.Geometry.Analytic.StrictTestDomain.RationalLimits

/-! # The strict scalar-normalization reduction for rational ideal descent -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

/-- The ideal specialization of Kiehl effectiveness for actual strict rational
covers over complete nontrivially normed ultrametric coefficient fields. -/
def StrictRationalIdealEffectivenessStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    (∃ c : K, 1 < ‖c‖) →
    ∀ (P : PresentedStrictAffinoidAlgebra K) (n : ℕ)
      (D : Fin n → StrictTestDomain.RationalData K P)
      (_hD : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus)
      (I : ∀ i : Fin n, Ideal (D i).algebra),
      (∀ i, IsClosed (I i : Set (D i).algebra)) →
      (∀ i j,
        (StrictTestDomain.RationalData.interLeft (D i) (D j)).restriction.closedIdealMap
            (I i) =
          (StrictTestDomain.RationalData.interRight (D i) (D j)).restriction.closedIdealMap
            (I j)) →
      ∀ i, (D i).baseMap.closedIdealMap
        (⨅ j, Ideal.comap (D j).baseMap.toAlgHom.toRingHom (I j)) = I i

/-- Descend the entire finite rational ideal-effectiveness theorem through
strict scalar normalization, retaining the original coefficient field,
positive radii, actual restriction maps and explicit contraction. -/
def StrictScalarIdealDescentStatement : Prop :=
  StrictRationalIdealEffectivenessStatement.{u} → RationalIdealEffectivenessStatement.{u}

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
