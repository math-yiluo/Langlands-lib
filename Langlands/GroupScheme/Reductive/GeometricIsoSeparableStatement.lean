import Langlands.GroupScheme.Reductive.Basic

/-! # Reductive groups isomorphic over `k̄` are isomorphic over a finite separable extension
(Milne 23.28) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 23.28: let `G` and `G'` be reductive groups over a field `k`. If their
base changes to the algebraic closure of `k` are isomorphic, then their base changes to some
finite separable field extension `L / k` are isomorphic. -/
def ReductiveGeometricIsoSeparableStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsConnectedReductive G' →
    Nonempty ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G ≅
      (GroupScheme.baseChange (toAlgebraicClosure k)).obj G') →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      Nonempty ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj G ≅
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj G')

end Langlands.GroupScheme
