import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Rational.QuasiSplitInnerForm
import Langlands.GroupScheme.Symplectic.Basic
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # Simply connected groups of type `C_n` are inner forms of `Sp_{2n}`: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `K` be a field and `G` an affine group scheme of locally finite type over `K`, with
index data `d` whose actual Cartan matrix, under a numbering `e` of its simple vertices by
`Fin n` with `2 ≤ n`, is the Cartan matrix of type `C_n`. If `G` is simply connected, then `G`
has a quasi-split inner-form presentation whose model group is isomorphic to the standard
symplectic group scheme `Sp_{2n}` over `K`. -/
def TypeCQuasiSplitInnerFormStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ)
    (e : d.Vertex ≃ Fin n),
    2 ≤ n → IsSimplyConnected G →
    (∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b)) →
      ∃ q : QuasiSplitInnerForm G, Nonempty (q.model ≅ Symplectic.groupScheme K n)

end Langlands.GroupScheme
