import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteFunctor
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.Algebra.Exact.Basic

/-! # Short exactness of the actual absolute-Galois character functor: statement -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme

/-- **Absolute-Galois character exactness**, the short-exact-sequence clause of
Milne, *Algebraic Groups* (2017), Theorem 12.23. The actual absolute-character functor
identifies closed subgroup inclusions with their represented fppf quotient sequences
and short exact sequences of finitely generated discrete Galois modules. No splitting
extension or diagonalizable model is supplied as a hypothesis. Torsion characters
and nonsmooth kernels are retained. -/
def MultiplicativeTypeAbsoluteExactnessStatement : Prop :=
  ∀ (k : Type u) [Field k] (N E Q : MultiplicativeTypeGroup k)
    (i : N ⟶ E) (q : E ⟶ Q),
    let X := MultiplicativeTypeGroup.characterFunctor k
    let pullQ := FGDiscreteGaloisModule.hom (X.map q.op)
    let pullN := FGDiscreteGaloisModule.hom (X.map i.op)
    (IsClosedSubgroup (CommGroupScheme.groupHom i.hom) ∧
      RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range (CommGroupScheme.groupHom i.hom))
        (CommGroupScheme.groupHom q.hom)) ↔
    (Function.Injective pullQ ∧ Function.Exact pullQ pullN ∧ Function.Surjective pullN)

end Langlands.GroupScheme
