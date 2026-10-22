import Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
import Langlands.Representation.Smooth.FixedVectors.Definitions

/-! # Fixed smooth functionals: proposition target -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The fixed-functional equivalence and restriction have natural evaluation. -/
def SmoothDualFixedVectorsStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ (ρ : Representation R G V) (K : OpenSubgroup G)
      (ℓ : fixedVectors (V := SmoothDual ρ) (smoothContragredient ρ) K.toSubgroup) (v : V),
      (smoothDualFixedEquiv ρ K ℓ).val v = smoothDualPairing ρ ℓ.val v) ∧
    (∀ (ρ : Representation R G V) (K : Subgroup G)
      (ℓ : fixedVectors (V := SmoothDual ρ) (smoothContragredient ρ) K) (v : fixedVectors ρ K),
      smoothDualFixedRestriction ρ K ℓ v = smoothDualPairing ρ ℓ.val v.val) ∧
    (∀ (ρ : Representation R G V) (K : OpenSubgroup G),
      smoothDualFixedRestriction ρ K.toSubgroup =
        (fixedVectors ρ K.toSubgroup).subtype.dualMap.comp
          ((fixedVectors ρ.dual K.toSubgroup).subtype.comp
            (smoothDualFixedEquiv ρ K).toLinearMap)) ∧
    (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (f : ρ.IntertwiningMap σ) (K : Subgroup G),
      (smoothDualFixedRestriction ρ K).comp
          (fixedVectorsMap (contragredientMap f) K) =
        (fixedVectorsMap f K).dualMap.comp (smoothDualFixedRestriction σ K))

end Langlands
