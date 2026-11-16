import Langlands.Global.RankinSelberg.UnfoldingDual

/-! # The Whittaker function of the dual cusp form

If the cusp form of a vector `xd` of a cuspidal realization `Td` is the dual
`φ̃(g) = φ(w_n ᵗg⁻¹)` of the cusp form `φ` of a vector `x` of a cuspidal realization `T`,
then the `ψ⁻¹`-Whittaker function of `xd` is the dual `W̃(g) = W(w_n ᵗg⁻¹)` of the
`ψ`-Whittaker function `W` of `x` (Cogdell 2004, pp.201 and 207).
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global AdelicSubgroupPoints Unfolding

local instance contragredientDualWhittakerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance contragredientDualWhittakerSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

local instance contragredientDualWhittakerUnipotentLocallyCompact (F : Type u) [Field F]
    [NumberField F] (n : ℕ) : LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- **The Whittaker function of the dual cusp form** (Cogdell 2004, pp.201 and 207). If
`φ_(xd) = φ̃_x`, then `W^(ψ⁻¹)_(xd) = W̃^ψ_x`. Both sides are the normalized integral of
`φ̃_x(n g) ψ_N(n)` over a fundamental domain of `N(F)` in `N(𝔸)`: the right side by
`Unfolding.dualCuspWhittaker_eq_setIntegral` for the character `ψ⁻¹`, the left side by
the coefficient formula `subgroupCharacterCoefficient_eq_setIntegral`. -/
theorem cuspWhittaker_inv_eq_dualFunction {r : ℕ}
    (T Td : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (x : T.Space) (xd : Td.Space)
    (hxd : cuspFunction F Td xd = dualFunction F (r + 1) (cuspFunction F T x)) :
    cuspWhittaker F Td ψ⁻¹ xd = dualFunction F (r + 1) (cuspWhittaker F T ψ x) := by
  funext y
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  have h := dualCuspWhittaker_eq_setIntegral F T ψ⁻¹ hψ' x y
  rw [inv_inv] at h
  rw [h]
  have hφm : Measurable (cuspFunction F Td xd) :=
    (Unfolding.continuous_cuspFunction F Td xd).measurable
  have hW := subgroupCharacterCoefficient_eq_setIntegral F (Scheme F (r + 1))
    (upperUnipotent F (r + 1)) (genericCharacter F r ψ⁻¹ fun _ => 1)
    (continuous_genericCharacter F r ψ⁻¹ hψ'.1 _).measurable
    (genericCharacter_rational_mul F r ψ⁻¹ hψ') (cuspFunction F Td xd) hφm
    (fun k z => Unfolding.cuspFunction_rational_mul F Td xd
      (mem_rationalSubgroup_of_unipotent F k) z) y
  have hconj : ∀ m : unipotentAdelic F (r + 1),
      starRingEnd ℂ (genericCharacter F r ψ⁻¹ (fun _ => 1) m) =
        (genericCharacter F r ψ⁻¹ (fun _ => 1) m)⁻¹ := fun m => by
    rw [genericCharacter_inv F r ψ hψ.2.2.2, Complex.conj_conj,
      ← genericCharacter_inv F r ψ hψ.2.2.2, genericCharacter_inv_eq_inv, inv_inv]
  simp_rw [hconj] at hW
  rw [show cuspWhittaker F Td ψ⁻¹ xd y = _ from hW, Complex.real_smul, hxd]

end Langlands.Global.RankinSelbergGlobal
