import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulus
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison

/-! # Closed principal relations in the scalar Laurent diagram -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus

/-- Closedness and the principal-relation comparison over the original strict bases. -/
def PrincipalRelationsStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    (∃ c : K, 1 < ‖c‖) →
    ∀ (P : PresentedStrictAffinoidAlgebra K) (f : ofStrict K P),
      let A := ofStrict K P
      let S := GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A
      let U := Algebra K A
      let C := GeneralizedTateAlgebra.constantAlgHom (PositivePolyradius.unit (Fin 1)) K A
      let T := GeneralizedTateAlgebra.X (PositivePolyradius.unit (Fin 1)) A 0
      let Jpos : Ideal S := Ideal.span ({T - C f} : Set S)
      let Jneg : Ideal S := Ideal.span ({C f * T - 1} : Set S)
      let J : Ideal U := Ideal.span ({annulusX K A - baseMap K A f} : Set U)
      IsClosed (Jpos : Set S) ∧
        IsClosed (Jneg : Set S) ∧
        IsClosed (J : Set U) ∧
        ∃ β : (Jpos × Jneg) ≃ₗ[K] J,
          ∀ (p : Jpos) (q : Jneg),
            (β (p, q) : U) = positive K A (p : S) - negative K A (q : S)

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus
