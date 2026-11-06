import Langlands.GroupScheme.Derived.MaximalTorusProductCentralizerReduction
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Surjectivity of derived-subgroup and maximal-torus multiplication -/

universe u

namespace Langlands.GroupScheme

/-- A connected reductive group over any field is the scheme-theoretic product
of its supplied full derived subgroup and any specified maximal torus. -/
theorem derivedMaximalTorusProductSurjectivity :
    DerivedMaximalTorusProductSurjectivityStatement.{u} :=
  derivedMaximalTorusProductSurjectivity_of_maximalTorusCentralizer
    (maximalTorusCentralizer_of_structuralInputs
      dynamicCentralizerReductive noTorusUnipotent solvableTorusQuotient)

end Langlands.GroupScheme
