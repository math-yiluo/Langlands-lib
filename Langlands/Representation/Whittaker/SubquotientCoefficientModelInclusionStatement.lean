import Langlands.Representation.Whittaker.FunctionalExactness

/-!
# Coefficient models of actual smooth subquotients

An equivariant functional on a quotient of an invariant subspace extends to
an equivariant functional on the ambient smooth representation. The resulting
coefficient models are nested in the unchanged equivariant function space.
-/

noncomputable section

namespace Langlands.Whittaker

universe uG uV uW

/-- A functional on an actual smooth subquotient has an ambient extension
whose coefficient model contains the original model. The subgroup and
character hypotheses are precisely those of smooth localization exactness. -/
def SubquotientCoefficientModelInclusionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (_hN : Jacquet.Localization.IsLimitOfCompactSubgroups N)
    (θ : N →* ℂˣ) (_hθ : IsLocallyConstant (fun n : N => (θ n : ℂ)))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    IsSmooth ρ →
    ∀ (U : Subrepresentation ρ) (q : U.toRepresentation.IntertwiningMap σ),
      Function.Surjective q →
      ∀ ℓ : functionals N θ σ,
        ∃ L : functionals N θ ρ,
          (∀ v : U.toSubmodule, L.val v.val = ℓ.val (q v)) ∧
          (ℓ.val ≠ 0 → L.val ≠ 0) ∧
          coefficientModel σ ℓ ≤ coefficientModel ρ L

end Langlands.Whittaker
