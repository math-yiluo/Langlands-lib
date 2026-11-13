import Langlands.GroupScheme.Rational.ClassFunctionsStronglyRegularFibres
import Langlands.GroupScheme.Rational.ClassFunctionsRationalLifting

/-! # Steinberg's class quotient of a simply connected quasi-split group

The witnesses are the canonical class-function quotient `ClassFunctions.quotient G` and
`ClassFunctions.rho G`. Property 1 is `ClassFunctions.rho_conjugation`, property 2 is
`ClassFunctions.stronglyRegularFibres` and property 3 is
`ClassFunctions.stronglyRegularRationalLifting`. -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Assembly of the three properties from the canonical class-function quotient, with the
rational-lifting property supplied as a hypothesis. -/
theorem quasiSplitSteinbergQuotient_of_rationalLifting
    (hlift : ClassFunctions.StronglyRegularRationalLiftingStatement.{u}) :
    QuasiSplitSteinbergQuotientStatement.{u} := by
  intro K _ G hsc hqs
  let _ : IsAffineHom G.X.hom := hqs.isConnectedReductive.isAffineHom
  refine ⟨ClassFunctions.quotient G, ClassFunctions.rho G, ?_, ?_, ?_⟩
  · intro Z g x
    exact ClassFunctions.rho_conjugation G g x
  · intro F _ _ y w S j hS hj hc hyw
    exact ClassFunctions.stronglyRegularFibres K G hsc hqs F y w S j hS hj hc hyw
  · intro v F _ _ w S j hS hj hc hv
    exact hlift K G hsc hqs v F w S j hS hj hc hv

/-- Steinberg's class quotient of a simply connected quasi-split group over an arbitrary
field (Steinberg 1965, 6.6, 6.10, 7.9, 9.4, 9.19; Borel–Springer 1968, 8.2, 8.6). -/
theorem quasiSplitSteinbergQuotient : QuasiSplitSteinbergQuotientStatement.{u} :=
  quasiSplitSteinbergQuotient_of_rationalLifting ClassFunctions.stronglyRegularRationalLifting

end Langlands.GroupScheme
