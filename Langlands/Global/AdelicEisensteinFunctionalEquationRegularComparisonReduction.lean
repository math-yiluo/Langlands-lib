import Langlands.Global.AdelicEisensteinFunctionalEquationRegularComparisonStatement
import Langlands.Global.AdelicEisensteinFunctionalEquationPropagation

/-! # Reduction of the Eisenstein functional equation to regular-patch comparison -/

universe u

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- The regular-patch comparison, applied beyond the finitely many agreement
bounds on the `Q` side, proves the exact published functional equation. -/
theorem eisensteinFunctionalEquationRegularComparisonReduction :
    EisensteinFunctionalEquationRegularComparisonReductionStatement.{u} := by
  classical
  intro compare F _ _ G P M U Q M' V A A' _ _ _ _ _ _
    p _ iU l a r _ _ _ hA hT q _ iV l' _ a' r' _ _ _ hA' hT' π' w c
    hG hU hV hπ' hw K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
    EP DP hEP hEPagree k ψ coeff D hψ hcoeff hMagree EQ DQ hEQ hEQagree
  choose R hR using hEQagree
  let T : ℝ := ∑ i, max (R i) 0
  have hbound (i : Fin k) : R i ≤ T :=
    (le_max_left (R i) 0).trans (Finset.single_le_sum (f := fun j => max (R j) 0)
      (fun j _ => le_max_right (R j) 0) (Finset.mem_univ i))
  obtain ⟨n, e, O, hO, hne, hpatch⟩ := compare F G P M U Q M' V A A'
    p iU l a r hA hT q iV l' a' r' hA' hT' π' w c hG hU hV hπ' hw
    K hK hK' rho hsmooth hcalc φ hmax hrho hφ EP DP hEP hEPagree k ψ coeff D hψ hcoeff hMagree T
  refine eisensteinFunctionalEquation_of_openAgreement r.isCompatible.levi r'.isCompatible.levi
    hπ' hw hEP hcoeff hEQ (fun g => ⟨n, e, O, hO, hne, ?_⟩)
  intro x hx
  obtain ⟨hreg, heq⟩ := hpatch x hx
  rw [heq g]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : r'.IsRegularParameter hA' hT' (R i) (weylParameter l c π' (e x)) :=
    fun α hα => lt_of_le_of_lt (hbound i) (hreg α hα)
  rw [hR i _ hi]

end Langlands.Global
