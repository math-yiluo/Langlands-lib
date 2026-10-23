import Langlands.AbelianScheme.Tate.PrimeComparison

/-! # Exact prime-product comparison statements for actual Tate limits -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- The canonical full coordinate map is a topological additive equivalence. -/
def FullPrimeProductComparison : Prop :=
  ∃ e : Full G T ≃+ PrimeProduct G T,
    e.toAddMonoidHom = toPrimeProduct G T ∧
      Continuous e ∧ Continuous e.symm

/-- The canonical away coordinate map is a topological additive equivalence. -/
def AwayPrimeProductComparison (m : ℕ) : Prop :=
  ∃ e : Away G T m ≃+ AwayPrimeProduct G T m,
    e.toAddMonoidHom = toAwayPrimeProduct G T m ∧
      Continuous e ∧ Continuous e.symm

/-- Full and all away decompositions of the actual torsion-section limits. -/
def PrimeProductComparisons : Prop :=
  FullPrimeProductComparison G T ∧ ∀ m : ℕ, AwayPrimeProductComparison G T m

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)

/-- Full comparison specialized to the actual abelian scheme. -/
abbrev FullPrimeProductComparison : Prop :=
  GroupScheme.Tate.PrimeComparison.FullPrimeProductComparison A.toGrp T

/-- Away comparison specialized to the actual abelian scheme. -/
abbrev AwayPrimeProductComparison (m : ℕ) : Prop :=
  GroupScheme.Tate.PrimeComparison.AwayPrimeProductComparison A.toGrp T m

/-- Both comparison families specialized to the actual abelian scheme. -/
abbrev PrimeProductComparisons : Prop :=
  GroupScheme.Tate.PrimeComparison.PrimeProductComparisons A.toGrp T

end Langlands.AbelianScheme.Tate.PrimeComparison
