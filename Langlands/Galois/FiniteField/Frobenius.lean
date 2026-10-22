import Langlands.Weil.Pullback
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Frobenius for finite fields and their actual absolute Galois groups

Arithmetic Frobenius is the cardinality-power automorphism; geometric
Frobenius is its inverse. No procyclicity or comparison equivalence is assumed.
-/

noncomputable section

namespace Langlands.Galois.FiniteField

universe u v

variable (k : Type u) [Field k] [Finite k]

/-- Unfold the absolute Galois group to its action on the specified algebraic
closure; this is the identity on both the group and its Krull topology. -/
def closureAction :
    Field.absoluteGaloisGroup k ≃ₜ* Gal(AlgebraicClosure k/k) :=
  ContinuousMulEquiv.refl _

/-- Arithmetic Frobenius on an algebraic extension of a finite field. -/
def arithmetic (K : Type v) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    Gal(K/k) :=
  letI := Fintype.ofFinite k
  _root_.FiniteField.frobeniusAlgEquivOfAlgebraic k K

/-- Geometric Frobenius, the inverse of arithmetic Frobenius. -/
def geometric (K : Type v) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    Gal(K/k) :=
  (arithmetic k K)⁻¹

/-- Arithmetic Frobenius in Mathlib's actual absolute Galois group. -/
def arithmeticFrobenius : Field.absoluteGaloisGroup k :=
  arithmetic k (AlgebraicClosure k)

/-- Geometric Frobenius in Mathlib's actual absolute Galois group. -/
def geometricFrobenius : Field.absoluteGaloisGroup k :=
  (arithmeticFrobenius k)⁻¹

/-- Restriction to any finite intermediate field of the algebraic closure.
Finite extensions of finite fields are Galois, so this is defined on the whole
absolute Galois group, with its existing Krull topology. -/
def finiteRestriction (L : IntermediateField k (AlgebraicClosure k))
    [FiniteDimensional k L] : Field.absoluteGaloisGroup k →ₜ* Gal(L/k) := by
  letI : Finite L := Module.finite_of_finite k
  letI : IsGalois k L := inferInstance
  exact
    { AlgEquiv.restrictNormalHom (F := k) (K₁ := AlgebraicClosure k) L with
      continuous_toFun := InfiniteGalois.restrictNormalHom_continuous L }

end Langlands.Galois.FiniteField
