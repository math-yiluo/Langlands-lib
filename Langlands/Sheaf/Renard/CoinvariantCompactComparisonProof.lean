import Langlands.Sheaf.Renard.CoinvariantStatements
import Langlands.Sheaf.Renard.ModuleProjectorComparisonProof

/-!
# Proof: the III.3.1 canonical compact-section comparison is an isomorphism

Renard (9 July 2026), III.3.1, paragraph after the Definition, printed p.83 / PDF p.89:
the compact sections of the coinvariant sheaf `F′` on `Y` are the coinvariants
`F_c(X)_G`.

The comparison `CoinvariantSheaf.compactComparison hX q hq hY` is by definition the
II.2.5 module comparison `ModuleProjectorComparison.moduleComparisonNat hY` whiskered by
the coinvariant-module functor `CoinvariantSheaf.modules hX q hq hY`. Its component at an
action sheaf `F` is therefore definitionally `moduleComparison hY M` for the nondegenerate
target-test module `M = (CoinvariantSheaf.modules hX q hq hY).obj F`, and the published
II.2.5 result `ModuleProjectorComparison.moduleComparisonIsIso` at `Y` and `M` gives the
isomorphism.
-/

namespace Langlands.Sheaf.Renard.CoinvariantStatements

open CategoryTheory

/-- Renard III.3.1: for every invariant continuous `q : X → Y` and every action sheaf `F`,
the canonical comparison from the compact-section coinvariants `F_c(X)_G` to the compact
sections of the coinvariant sheaf `F′` is an isomorphism of nondegenerate target-test
modules. It is the II.2.5 module comparison at the coinvariant module. -/
theorem compactComparisonStatement : CompactComparisonStatement := by
  intro G _ _ _ _ X Y _ _ _ _ hX q hq hY F
  exact ModuleProjectorComparison.moduleComparisonIsIso Y hY
    ((CoinvariantSheaf.modules hX q hq hY).obj F)

end Langlands.Sheaf.Renard.CoinvariantStatements
