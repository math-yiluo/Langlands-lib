import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # The distinguished vertices of a symplectic group of an antihermitian form: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `G` be a simply connected absolutely almost simple group over a field `K`, with index
data `d` whose actual Cartan matrix, under a numbering `e` of its simple vertices by `Fin n`
with `2 ≤ n`, is the Cartan matrix of type `C_n`. Suppose `G` is isomorphic to the symplectic
group `σ.symplecticGroup H` of an invertible trace-valued `σ`-antihermitian Gram matrix
`H ∈ M_m(D)`, where `D` is a central division `K`-algebra of degree `degree` with
`m * degree = 2 * n`, and `σ` is an involution of the first kind of `D` whose symmetric space
has dimension `degree * (degree + 1) / 2`. Then a vertex `a` is distinguished exactly when
`(e a).val + 1 = j * degree` for some `1 ≤ j ≤ σ.wittIndex H`. -/
def TypeCDistinguishedVerticesStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ)
    (e : d.Vertex ≃ Fin n),
    2 ≤ n → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b)) →
    ∀ (degree m : ℕ) [NeZero m] (D : Type u) [DivisionRing D] [Algebra K D]
      [Algebra.IsCentral K D] [FiniteDimensional K D],
      0 < degree → m * degree = 2 * n → Module.finrank K D = degree ^ 2 →
      ∀ σ : Quaternionic.FirstKindInvolution K D,
        Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 →
        ∀ H : Matrix (Fin m) (Fin m) D, σ.IsAntihermitian H → IsUnit H →
          Nonempty (G ≅ σ.symplecticGroup H) →
            ∀ a : d.Vertex, a ∈ d.distinguishedVertices ↔
              ∃ j : ℕ, 1 ≤ j ∧ j ≤ σ.wittIndex H ∧ (e a).val + 1 = j * degree

end Langlands.GroupScheme
