import Langlands.AbelianScheme.Rational
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! # Integral Hom in finite-dimensional rational subspaces -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Integral homomorphisms in any finite-dimensional rational Hom subspace
form a finitely generated integer module. This is a local statement: no
finite-dimensionality of the whole rational Hom space is assumed or asserted. -/
def HomLocalLatticeStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A B : AbelianScheme (Spec (CommRingCat.of k)))
    (V : Submodule ℚ (Hom0 A B)), V.FG →
    ((V.restrictScalars ℤ).comap (homToHom0 (A := A) (B := B))).FG

end Langlands.AbelianScheme
