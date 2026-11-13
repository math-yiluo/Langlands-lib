import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Reductive.AlmostSimple
import Mathlib.LinearAlgebra.RootSystem.Irreducible

/-! # Statement: the relative root system of an almost-simple group is irreducible -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

/-- **Irreducibility of the relative root system** (Borel–Tits 1965, Corollary 5.11).
Let `G` be an almost-simple group over a field `k`, and let `i : T ⟶ G` be a maximal
split torus with at least one relative root. Let `P` be a root pairing, indexed by any
type `J : Type u`, on the rational span `relativeRootSpan i` of the relative roots, with
coroots in its rational dual. Suppose that the pairing of `P` is evaluation and that the
roots of `P` are exactly the images `1 ⊗ α` of the relative roots `α`. Then `P` is
irreducible in the sense of Mathlib's `RootPairing.IsIrreducible`. -/
def RelativeRootSystemIrreducibleStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsAlmostSimple G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    haveI := hG.isSemisimple.isConnectedReductive.isAffineHom
    (relativeRoots i).Nonempty →
    ∀ (J : Type u)
      (P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))),
      P.toLinearMap = Module.Dual.eval ℚ (relativeRootSpan i) →
      Subtype.val '' Set.range P.root = toRat '' relativeRoots i →
      P.IsIrreducible

end Langlands.GroupScheme
