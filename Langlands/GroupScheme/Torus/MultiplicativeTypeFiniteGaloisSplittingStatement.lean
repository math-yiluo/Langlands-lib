import Langlands.GroupScheme.Torus.MultiplicativeType
import Mathlib.FieldTheory.Galois.Basic

/-! # Statement: groups of multiplicative type over a field split over a finite Galois extension -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every group `H` of multiplicative type over a field `k` (in the sense of
`IsMultiplicativeType`: diagonalizable, with finitely generated character group, after base
change to some field extension) becomes diagonalizable, with a finitely generated character
group, after base change to a finite Galois extension `K / k` (Milne, *Algebraic Groups*
(2017), Corollary 12.19; Conrad, *Reductive group schemes* (2014), Lemma B.1.5; SGA 3, X,
1.4). -/
def MultiplicativeTypeFiniteGaloisSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k))), IsMultiplicativeType H →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
        Nonempty (((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) ≅
            (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)

end Langlands.GroupScheme
