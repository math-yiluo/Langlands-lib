import Langlands.GroupScheme.Multiplicative
import Mathlib.RingTheory.AdjoinRoot

/-! # Affine presentation of the actual roots-of-unity kernel -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For positive `n`, the actual roots-of-unity kernel over `Spec A` is isomorphic,
over `Spec A`, to the spectrum of `A[X] / (X^n - 1)` with its canonical structure map.
This proposition is a statement target, not a proof. -/
def MuAffinePresentationStatement : Prop :=
  ∀ (A : CommRingCat.{u}) (n : ℕ), 0 < n →
    Nonempty ((mu (Spec A) n).X ≅
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - 1))))))

end Langlands.GroupScheme
