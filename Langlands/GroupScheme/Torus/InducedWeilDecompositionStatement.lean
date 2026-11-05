import Langlands.GroupScheme.Torus.Induced
import Langlands.GroupScheme.Torus.WeilRestrictionCommutative

/-! # Statement: induced tori as Weil restrictions of product algebras -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

universe u

/-- An induced torus split by the prescribed finite Galois extension `L/k` is the
Weil restriction of `𝔾ₘ` from a finite product of intermediate fields of `L/k`.
This is a statement only; the empty product is allowed. -/
def InducedTorusWeilDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] (L : Type u) [Field L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus (GaloisPointComparison.baseChanged k L T.toGrp) →
    IsInducedTorus T →
    ∃ (n : ℕ) (E : Fin n → IntermediateField k L),
      Nonempty (T ≅ WeilGm.commGroupScheme (CommRingCat.of k) (∀ i, E i))

end Langlands.GroupScheme
