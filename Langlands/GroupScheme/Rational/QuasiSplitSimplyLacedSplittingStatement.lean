import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # A reduced simply-laced relative root system forces a quasi-split group to split -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The full set of relative roots, in its rational span, admits a reduced
crystallographic root system with the evaluation pairing and symmetric
root-coroot pairing. No roots are discarded to obtain a reduced subsystem. -/
def HasReducedSimplyLacedRelativeRootSystem (i : S.toGrp ⟶ G)
    [IsAffineHom G.X.hom] : Prop :=
  ∃ (J : Type u) (_ : Finite J)
    (P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))),
    P.IsRootSystem ∧ P.IsCrystallographic ∧ P.IsReduced ∧
    P.toLinearMap = Module.Dual.eval ℚ (relativeRootSpan i) ∧
    Subtype.val '' Set.range P.root = toRat '' relativeRoots i ∧
    ∀ a b, P.pairing a b = P.pairing b a

/-- A quasi-split absolutely almost-simple group over any field is split if its
full relative root system is reduced and simply laced: each maximal split torus
with that property is already a maximal torus. This is a derived folding
criterion, stated here without a proof. -/
def QuasiSplitSimplyLacedSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsQuasiSplit G), IsAbsolutelyAlmostSimple G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : S.toGrp ⟶ G), IsMaximalSplitTorus i →
      haveI := hG.isConnectedReductive.isAffineHom
      HasReducedSimplyLacedRelativeRootSystem i → IsMaximalTorus i

end Langlands.GroupScheme
