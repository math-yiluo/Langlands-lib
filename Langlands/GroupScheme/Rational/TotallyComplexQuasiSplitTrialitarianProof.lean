import Langlands.GroupScheme.Rational.TotallyComplexTrialitarianCubicSplitTorusReduction
import Langlands.GroupScheme.Rational.TrialitarianCubicSplitTorusProof

/-! # Cohomology vanishing for quasi-split trialitarian groups over totally complex number fields -/

universe u

namespace Langlands.GroupScheme

/-- Every finite Galois cover cocycle of a simply connected, absolutely almost-simple,
quasi-split trialitarian group over a totally complex number field is a coboundary on that cover. -/
theorem totallyComplexQuasiSplitTrialitarianCocycleVanishing :
    TotallyComplexQuasiSplitTrialitarianCocycleVanishingStatement.{u} :=
  totallyComplexQuasiSplitTrialitarian_of_cubicSplitTorus trialitarianCubicSplitMaximalTorus

end Langlands.GroupScheme
