import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChangeBasic
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChangeColimits

/-! # Murre's conditions are stable under base change -/

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

/-- Murre, Bourbaki exp. 294, Section 2: the conditions of the criterion are stable under
base change along any morphism of schemes. -/
theorem murreBaseChange : MurreBaseChangeStatement.{u, v} := by
  intro S S' g F ⟨h0, h1a, h1b, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨BaseChange.smallValues g F h0, BaseChange.zariskiSheaf g F h1a,
    BaseChange.faithfullyFlatSheaf g F h1b, BaseChange.filteredColimits h1a h2 g,
    BaseChange.adicLimits g F h3, BaseChange.artinianLifting g F h4,
    BaseChange.nilpotentInjective g F h5, BaseChange.valuativeSeparation g F h6,
    BaseChange.oneDimensionalLifting g F h7, BaseChange.genericNonLifting g F h8⟩

end Langlands.AlgebraicGeometry.UnramifiedFunctor
