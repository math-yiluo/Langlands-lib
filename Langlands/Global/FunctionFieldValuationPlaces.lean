import Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Langlands.AnthropicFLT.Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
import Mathlib.NumberTheory.FunctionField
import Mathlib.FieldTheory.Finite.Valuation

/-! # All valuation-subring places of function fields with finite constants -/

noncomputable section

universe u

open IntermediateField Polynomial AlgebraicCurve
open scoped IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.CurveModel

namespace Langlands.Global

section Principal

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

private theorem principal_valuationSubring_of_mem_parameter
    (s : F) [FiniteDimensional k⟮s⟯ F]
    (O : ValuationSubring F) (hK : ∀ a : k, algebraMap k F a ∈ O)
    (hs : s ∈ O) : IsPrincipalIdealRing O := by
  let R := Algebra.adjoin k ({s} : Set F)
  have hR (a : R) : algebraMap R F a ∈ O :=
    CurveModel.adjoin_le_valuationSubring O hK
      (Set.singleton_subset_iff.mpr hs) a.property
  let B : Subalgebra R F := { O.toSubring with algebraMap_mem' := hR }
  have hB : IsNoetherianRing B :=
    (Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
      (K := k⟮s⟯) B).1
  have : IsNoetherianRing O := hB
  infer_instance

/-- Every valuation ring of a one-variable function field that contains its
constant field is principal. The supplied presentation need not be separable. -/
theorem functionField_valuationSubring_principal
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (O : ValuationSubring F) (hK : ∀ a : k, algebraMap k F a ∈ O) :
    IsPrincipalIdealRing O := by
  let s : F := algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)
  let : FiniteDimensional k⟮s⟯ F := FunctionField.FiniteDimensional.adjoin_algebraMap_X
  rcases O.mem_or_inv_mem s with hs | hs
  · exact principal_valuationSubring_of_mem_parameter k F s O hK hs
  · have hinv : k⟮s⁻¹⟯ = k⟮s⟯ :=
      le_antisymm
        (adjoin_simple_le_iff.mpr (inv_mem (mem_adjoin_simple_self k s)))
        (adjoin_simple_le_iff.mpr (by
          simpa using inv_mem (mem_adjoin_simple_self k s⁻¹)))
    let : FiniteDimensional k⟮s⁻¹⟯ F := by rw [hinv]; infer_instance
    exact principal_valuationSubring_of_mem_parameter k F s⁻¹ O hK hs

/-- Promote an arbitrary nontrivial constant-field valuation ring to an actual
curve place, using the proved automatic principal-ideal property. -/
def functionFieldPlaceOfValuationSubring
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (O : ValuationSubring F) (hK : ∀ a : k, algebraMap k F a ∈ O) (hO : O ≠ ⊤) :
    Place k F where
  toValuationSubring := O
  algebraMap_mem' := hK
  ne_top' := hO
  isPrincipalIdealRing' := functionField_valuationSubring_principal k F O hK

@[simp]
theorem functionFieldPlaceOfValuationSubring_toValuationSubring
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (O : ValuationSubring F) (hK : ∀ a : k, algebraMap k F a ∈ O) (hO : O ≠ ⊤) :
    (functionFieldPlaceOfValuationSubring k F O hK hO).toValuationSubring = O := rfl

end Principal

section FiniteConstants

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]

/-- Every valuation subring contains the finite constant field. -/
theorem finiteConstants_mem_valuationSubring (O : ValuationSubring F) (a : k) :
    algebraMap k F a ∈ O :=
  O.mem_of_valuation_le_one _ (FiniteField.valuation_algebraMap_le_one O.valuation a)

/-- All nontrivial valuation rings of `F`, with no discreteness condition. -/
abbrev ValuationRingPlace := {O : ValuationSubring F // O ≠ ⊤}

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- The curve-place model equals the model consisting of all nontrivial valuation
rings of a function field over a finite field. -/
def curvePlaceValuationRingEquiv : Place k F ≃ ValuationRingPlace F where
  toFun p := ⟨p.toValuationSubring, p.ne_top'⟩
  invFun O := functionFieldPlaceOfValuationSubring k F O.val
    (finiteConstants_mem_valuationSubring k F O.val) O.property
  left_inv _p := Place.ext rfl
  right_inv _O := Subtype.ext rfl

@[simp]
theorem curvePlaceValuationRingEquiv_apply (p : Place k F) :
    (curvePlaceValuationRingEquiv k F p).val = p.toValuationSubring := rfl

@[simp]
theorem curvePlaceValuationRingEquiv_symm_apply (O : ValuationRingPlace F) :
    ((curvePlaceValuationRingEquiv k F).symm O).toValuationSubring = O.val := rfl

end FiniteConstants

end Langlands.Global
