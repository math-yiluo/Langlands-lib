import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Mathlib.LinearAlgebra.RootSystem.Irreducible

/-! # Absolute almost-simplicity and irreducibility of the absolute root system -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

/-- Conrad, *Reductive group schemes*, Corollary 5.1.18: a nontrivial semisimple group `G`
over a field `k` is absolutely almost simple exactly when its absolute root system is
irreducible. The absolute root system is that of the base change `G_{k̄}` to the
algebraic closure with respect to a maximal torus `i : T ⟶ G_{k̄}` (over `k̄` every torus
is split, so `i` is a maximal split torus): every root pairing `P` on the rational span
of the roots, with evaluation as pairing and with the roots as its roots, is
irreducible in the sense of Mathlib's `RootPairing.IsIrreducible`.
This module states the proposition and does not prove it. -/
def AbsolutelyAlmostSimpleIrreducibleStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsSemisimple G),
    SubgroupFunctor.range (𝟙 G) ≠ ⊥ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
      (i : T.toGrp ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G),
      IsMaximalSplitTorus i →
      haveI := hG.isConnectedReductive.isAffineHom
      haveI : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom :=
        inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (toAlgebraicClosure k)))
      ∀ (J : Type u)
        (P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))),
        P.toLinearMap = Module.Dual.eval ℚ (relativeRootSpan i) →
        Subtype.val '' Set.range P.root = toRat '' relativeRoots i →
        (IsAbsolutelyAlmostSimple G ↔ P.IsIrreducible)

end Langlands.GroupScheme
