import Langlands.Sheaf.Renard.CoinvariantSheaf
import Langlands.Sheaf.Renard.InvariantFibres

/-!
# Renard III.3.1: the actual coinvariant sheaf and its fibre/distribution assertions

All statements are closed Prop-valued targets over the original quotient,
actual fibre restriction, actual compact sections and ordinary original stalk.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.CoinvariantStatements

open CategoryTheory
open Langlands.Sheaf.Renard.SectionActions

/-- The source's compact-section identification uses the existing canonical
original-module comparison, not a supplied isomorphism. -/
def CompactComparisonStatement : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (_hG : Langlands.Topology.IsLocallyProfinite G)
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction G X] [ContinuousSMul G X]
    (hX : Langlands.Topology.IsLocallyProfinite X)
    (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : Langlands.Topology.IsLocallyProfinite Y)
    (F : ActionSheaf G X),
    IsIso ((CoinvariantSheaf.compactComparison hX q hq hY).app F)

/-- Renard III.3.1 Proposition: the original stalk of F-prime is naturally
isomorphic to the original compact-fibre representation coinvariants. -/
def FibreCoinvariantStatement : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (_hG : Langlands.Topology.IsLocallyProfinite G)
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction G X] [ContinuousSMul G X]
    (hX : Langlands.Topology.IsLocallyProfinite X)
    (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : Langlands.Topology.IsLocallyProfinite Y) (y : Y),
    Nonempty ((CoinvariantSheaf.functor hX q hq hY ⋙
        TopCat.Sheaf.forget (ModuleCat.{0} ℂ) (TopCat.of Y) ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) y) ≅
      InvariantFibres.coinvariants q hq y)

/-- Renard III.3.1 Corollary: absence of invariant algebraic distributions
on every actual restricted fibre implies absence on all original compact sections. -/
def NoInvariantDistributionsStatement : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (_hG : Langlands.Topology.IsLocallyProfinite G)
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction G X] [ContinuousSMul G X]
    (_hX : Langlands.Topology.IsLocallyProfinite X)
    (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (_hY : Langlands.Topology.IsLocallyProfinite Y) (F : ActionSheaf G X),
    (∀ y : Y,
      letI := InvariantFibres.fibreAction q hq y
      letI := InvariantFibres.fibreContinuousSMul q hq y
      ∀ T : Distribution ((InvariantFibres.restriction q hq y).obj F),
        IsInvariantDistribution ((InvariantFibres.restriction q hq y).obj F) T → T = 0) →
    ∀ T : Distribution F, IsInvariantDistribution F T → T = 0

/-- The canonical compact comparison, natural fibre Proposition and distribution Corollary. -/
def Statements : Prop :=
  CompactComparisonStatement ∧ FibreCoinvariantStatement ∧ NoInvariantDistributionsStatement

end Langlands.Sheaf.Renard.CoinvariantStatements
