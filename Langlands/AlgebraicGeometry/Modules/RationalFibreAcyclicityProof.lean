import Langlands.AlgebraicGeometry.Modules.RationalFibreAcyclicityStatement
import Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsProof

/-! # Open-local rational-fibre acyclicity: proof -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- Vanishing on all rational fibres over an open set implies vanishing there
of every higher direct image of a line bundle in a smooth proper family. -/
theorem rationalFibreAcyclicity : RationalFibreAcyclicityStatement.{u} := by
  intro K _ _ X Y g hg f hf hp Q U hQ n
  let : LocallyOfFiniteType g := hg
  let : Smooth f := hf
  let : IsProper f := hp
  exact DerivedSections.isZero_pullback_higherDirectImage_of_rationalFibres
    universalPerfectSections K g f Q U hQ n

end Langlands.AlgebraicGeometry.Modules
