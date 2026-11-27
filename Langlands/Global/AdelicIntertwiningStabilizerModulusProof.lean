import Langlands.Global.AdelicIntertwiningLeviHaarBalance
import Langlands.Global.AdelicIntertwiningStabilizerModulusStatement

/-! # The normalized Haar factor of the intertwining quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- The quotient Haar factor is the target half modulus times the inverse source half modulus. -/
theorem intertwiningStabilizerModulus : IntertwiningStabilizerModulusStatement.{u} := by
  intro F _ _ G P M U Q M' V _ _ _ _ _ _ _ _ _ p iU l q iV l' _ w c
    hG hp hU hl hq hV hl' hw hi hVu hUn hVn m
  have h := intertwiningLeviHaarBalance_of_parabolics hG hp hU hl hq hV hl' hw m
  change intertwiningLeviHaarFactor iU iV hw hUn hVn hi hVu m = _
  have hInv (x : AdelicGroupPoints F P) :
      parameterPower F P (halfModulusParameter F P) x *
        parameterPower F P (-halfModulusParameter F P) x = 1 := by
    simp only [parameterPower, map_neg, LinearMap.neg_apply, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero]
  rw [map_comp_apply_of_hom, ← h, mul_assoc, hInv, mul_one]

end Langlands.Global
