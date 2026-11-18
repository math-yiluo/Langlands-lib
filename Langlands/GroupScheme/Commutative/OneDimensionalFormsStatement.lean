import Langlands.GroupScheme.Multiplicative
import Langlands.GroupScheme.VectorGroupQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # Smooth connected groups of dimension one are forms of `𝔾ₘ` or `𝔾ₐ` (Milne 16.16) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.16: let `G` be a smooth connected affine group scheme of dimension one
over a field `k`. Either `G` becomes isomorphic to `𝔾ₘ` over a finite separable extension of `k`,
or it becomes isomorphic to `𝔾ₐ` over a finite purely inseparable extension of `k`. Over an
algebraically closed field, `G` is isomorphic to `𝔾ₘ` or to `𝔾ₐ`. -/
def OneDimensionalGroupFormsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left →
      ((∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
          FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
            Nonempty ((GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
                (Gm (Spec (CommRingCat.of K))).toGrp)) ∨
        (∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
          FiniteDimensional k K ∧ IsPurelyInseparable k K ∧
            Nonempty ((GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
                VectorGroup.groupScheme (CommRingCat.of K) 1))) ∧
      (IsAlgClosed k →
        Nonempty (G ≅ (Gm (Spec (CommRingCat.of k))).toGrp) ∨
          Nonempty (G ≅ VectorGroup.groupScheme (CommRingCat.of k) 1))

end Langlands.GroupScheme
