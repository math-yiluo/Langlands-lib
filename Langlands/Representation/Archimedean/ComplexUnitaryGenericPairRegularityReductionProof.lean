import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement

/-!
# Reduction of the complex case of Getz–Hahn, Theorem 11.5.2

A proof of `Langlands.Archimedean.ComplexUnitaryGenericPairRegularityReductionStatement`: the
exponent bound `|Re t| < 1/2` for unitary generic modules at both carrier universes and the
right half-plane regularity of complex pair `L`-factors give the complex case of Getz–Hahn
(2024), Theorem 11.5.2, on `Re(s) ≥ 1`. The three inputs are hypotheses of the statement;
none is proved here. See the paired Markdown.
-/

set_option autoImplicit false

universe uV uW

namespace Langlands.Archimedean

/-- **Reduction of the complex case of Getz–Hahn, Theorem 11.5.2.** For characters `x` of
`ds` and `y` of `ds'`, the exponent bounds give `Re(t_x), Re(t_y) > -1/2`, so
`Re(s) + Re(t_x) + Re(t_y) > 1 - 1/2 - 1/2 = 0` when `Re(s) ≥ 1`, and the regularity
hypothesis applies. -/
theorem complexUnitaryGenericPairRegularityReduction :
    ComplexUnitaryGenericPairRegularityReductionStatement.{uV, uW} := by
  intro hV hW hreg n m V _ _ W _ _ ρ π ρ' π' ds ds' hG hI hA hGen hU hP hG' hI' hA' hGen' hU'
    hP' s hs
  refine hreg ds ds' s fun x hx y hy => ?_
  have hx' := (abs_lt.mp (hV n V ρ π ds hG hI hA hGen hU hP x hx)).1
  have hy' := (abs_lt.mp (hW m W ρ' π' ds' hG' hI' hA' hGen' hU' hP' y hy)).1
  linarith

end Langlands.Archimedean
