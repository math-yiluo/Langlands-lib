import Langlands.GroupScheme.Torus.Lattice
import Mathlib.FieldTheory.Galois.Basic

/-! # Statement: every torus over a field splits over a finite Galois extension -/

open AlgebraicGeometry

namespace Langlands.GroupScheme

universe u

/-- Every torus `T` over a field `k` (in the sense of `IsTorus`: split after base change to some
field extension) becomes a split torus after base change to a finite Galois extension `K / k`
(Milne 12.18, 12.19; SGA 3 X 1.4). -/
def TorusFiniteGaloisSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : GroupScheme (Spec (CommRingCat.of k))), IsTorus T →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      IsSplitTorus ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)

end Langlands.GroupScheme
