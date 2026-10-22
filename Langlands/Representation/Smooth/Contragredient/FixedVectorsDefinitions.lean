import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions

/-! # Fixed functionals and restriction to fixed vectors -/

noncomputable section

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

/-- An open-subgroup-fixed algebraic functional is already smooth. -/
def smoothDualFixedEquiv (ρ : Representation R G V) (K : OpenSubgroup G) :
    fixedVectors (V := SmoothDual ρ) (smoothContragredient ρ) K.toSubgroup ≃ₗ[R]
      fixedVectors ρ.dual K.toSubgroup :=
  smoothPartFixedVectorsEquiv ρ.dual K

/-- Restrict a subgroup-fixed smooth functional to the fixed-vector submodule.
No bijectivity is asserted by this construction. -/
def smoothDualFixedRestriction (ρ : Representation R G V) (K : Subgroup G) :
    fixedVectors (V := SmoothDual ρ) (smoothContragredient ρ) K →ₗ[R]
      Module.Dual R (fixedVectors ρ K) where
  toFun ℓ := ℓ.val.val.comp (fixedVectors ρ K).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Langlands
