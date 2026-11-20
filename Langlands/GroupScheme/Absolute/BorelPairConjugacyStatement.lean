import Langlands.GroupScheme.Absolute.Borel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Conjugacy of Borel pairs (Milne 17.13) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 17.13: let `G` be a smooth connected affine group over an
algebraically closed field `k`. For any two Borel pairs `(i, j)` and `(i', j')` of `G` there are
a single point `g ∈ G(k)` and isomorphisms `φ : B ≅ B'`, `ψ : T ≅ T'` such that conjugation by
`g` carries `i` to `φ ≫ i'` and `j` to `ψ ≫ j'`. -/
def BorelPairConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B B' : GroupScheme (Spec (CommRingCat.of k)))
    (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : B ⟶ G) (j : T.toGrp ⟶ G) (i' : B' ⟶ G) (j' : T'.toGrp ⟶ G),
    IsBorelPair i j → IsBorelPair i' j' →
      ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (φ : B ≅ B') (ψ : T ≅ T'),
        i ≫ (G.innerIso g).hom = φ.hom ≫ i' ∧
          j ≫ (G.innerIso g).hom = CommGroupScheme.groupHom ψ.hom ≫ j'

end Langlands.GroupScheme
