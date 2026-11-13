import Langlands.GroupScheme.Descent.FiniteUnramifiedGroupModel

/-! # Actual integer rings at finite unramified stages -/

noncomputable section

universe u

open scoped ValuativeRel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteUnramified

open Langlands.LocalGalois Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance coefficientsNormedField : NontriviallyNormedField F := localNormedField F
local instance coefficientsUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance coefficientsComplete : CompleteSpace F := localNormedField_complete F

/-- The coefficient subring inside the maximal unramified integers is the
actual spectral integer ring of the intermediate field. -/
def integerCoefficientsEquiv (E : IntermediateField F (SeparableClosure F))
    (hE : E ≤ inertiaFixedField F) :
    integerCoefficients F E ≃+* extensionIntegers F E where
  toFun x := ⟨⟨x.1.1.1, x.2⟩, by
    change spectralNorm F E (⟨x.1.1.1, x.2⟩ : E) ≤ 1
    rw [spectralNorm.eq_of_tower (L := SeparableClosure F)]
    exact x.1.2⟩
  invFun x := ⟨⟨⟨x.1.1, hE x.1.2⟩, by
    change spectralNorm F (SeparableClosure F)
      (algebraMap E (SeparableClosure F) (x : E)) ≤ 1
    rw [← spectralNorm.eq_of_tower (K := F) (L := SeparableClosure F) x.1]
    exact x.2⟩, x.1.2⟩
  left_inv x := Subtype.ext (Subtype.ext (Subtype.ext rfl))
  right_inv x := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem integerCoefficientsEquiv_coe
    (E : IntermediateField F (SeparableClosure F))
    (hE : E ≤ inertiaFixedField F) (x : integerCoefficients F E) :
    ((integerCoefficientsEquiv F E hE x : E) : SeparableClosure F) =
      fixedFieldToSepClosure F (x.1 : inertiaFixedField F) := rfl

/-- The actual action of a finite-stage field automorphism on its integer
coefficient ring. -/
def integerCoefficientsAut (E : IntermediateField F (SeparableClosure F))
    (hE : E ≤ inertiaFixedField F) (σ : E ≃ₐ[F] E) :
    integerCoefficients F E ≃+* integerCoefficients F E :=
  (integerCoefficientsEquiv F E hE).trans
    ((integerAut F E σ).toRingEquiv.trans (integerCoefficientsEquiv F E hE).symm)

@[simp]
theorem integerCoefficientsAut_coe
    (E : IntermediateField F (SeparableClosure F))
    (hE : E ≤ inertiaFixedField F) (σ : E ≃ₐ[F] E)
    (x : integerCoefficients F E) :
    ((integerCoefficientsEquiv F E hE (integerCoefficientsAut F E hE σ x) : E) :
      SeparableClosure F) = σ (integerCoefficientsEquiv F E hE x) := by
  simp only [integerCoefficientsAut, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply]
  rfl

end Langlands.GroupScheme.Descent.FiniteUnramified
