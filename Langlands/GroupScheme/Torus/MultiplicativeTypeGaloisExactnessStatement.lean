import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.Algebra.Exact.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Finiteness

/-! # Finite Galois character exactness for groups of multiplicative type: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Finite Galois character exactness for groups of multiplicative type**, derived from
Milne, *Algebraic Groups* (2017), Theorems 12.9(b) and 12.23. Given three commutative
group schemes with finitely generated diagonalizable models over a common finite Galois
extension, two homomorphisms form a short exact sequence of fppf sheaves if and only if
their actual character pullbacks form a short exact sequence compatible with the canonical
Galois actions. The character groups may have torsion, and the kernel need not be smooth. -/
def MultiplicativeTypeGaloisExactnessStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (N E Q : CommGroupScheme (Spec (CommRingCat.of k)))
    (M_N M_E M_Q : Type u) [AddCommGroup M_N] [AddCommGroup M_E] [AddCommGroup M_Q]
    [AddGroup.FG M_N] [AddGroup.FG M_E] [AddGroup.FG M_Q]
    (_n : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj N ≅
      Diagonalizable.groupScheme (CommRingCat.of L) M_N)
    (_e : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj E ≅
      Diagonalizable.groupScheme (CommRingCat.of L) M_E)
    (_q : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj Q ≅
      Diagonalizable.groupScheme (CommRingCat.of L) M_Q)
    (i : N ⟶ E) (q : E ⟶ Q),
    let BC := CommGroupScheme.baseChange (algebraBaseMap k L)
    let pullQ : characterLattice (BC.obj Q) → characterLattice (BC.obj E) :=
      fun χ => BC.map q ≫ χ
    let pullN : characterLattice (BC.obj E) → characterLattice (BC.obj N) :=
      fun χ => BC.map i ≫ χ
    (IsClosedSubgroup (CommGroupScheme.groupHom i) ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (CommGroupScheme.groupHom i))
        (CommGroupScheme.groupHom q)) ↔
    ((∀ (σ : L ≃ₐ[k] L) (χ : characterLattice (BC.obj Q)),
        pullQ (characterLattice.galoisRepresentation k L Q σ χ) =
          characterLattice.galoisRepresentation k L E σ (pullQ χ)) ∧
      (∀ (σ : L ≃ₐ[k] L) (χ : characterLattice (BC.obj E)),
        pullN (characterLattice.galoisRepresentation k L E σ χ) =
          characterLattice.galoisRepresentation k L N σ (pullN χ)) ∧
      Function.Injective pullQ ∧ Function.Exact pullQ pullN ∧ Function.Surjective pullN)

end Langlands.GroupScheme
