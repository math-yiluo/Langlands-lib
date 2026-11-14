import Langlands.GroupScheme.Rational.QuasiSplitRegularConjugateReduction
import Langlands.GroupScheme.Rational.QuasiSplitRegularClassRational
import Langlands.GroupScheme.Rational.RegularConjugateFiniteGaloisProof

/-! # Rational representatives of strongly regular classes of inner forms (Steinberg §10) -/

universe u

namespace Langlands.GroupScheme

/-- **Steinberg's rational conjugacy theorem for inner twists.** Let `G` be a simply connected
quasi-split group over a field `K`, and `H` an inner twist of `G` split by a finite Galois
extension `L/K`. Every `K`-rational point `y` of `H` whose all-test centralizer lies in a closed
`K`-torus is conjugate, over a finite Galois extension `L'/K` that receives a `K`-embedding of
`L`, to a `K`-rational point `x` of `G` whose all-test centralizer also lies in a closed
`K`-torus. -/
theorem quasiSplitSimplyConnectedRegularConjugate :
    QuasiSplitSimplyConnectedRegularConjugateStatement.{u} :=
  quasiSplitSimplyConnectedRegularConjugate_of_classRational quasiSplitRegularClassRational
    regularConjugateFiniteGalois

end Langlands.GroupScheme
