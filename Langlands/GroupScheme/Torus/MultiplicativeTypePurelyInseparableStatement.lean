import Langlands.GroupScheme.Torus.MultiplicativeType
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # Statement: purely inseparable extensions do not change groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Purely inseparable descent for groups of multiplicative type** (Milne, *Algebraic Groups*
(2017), Corollaries 12.20 and 12.25). Let `k'` be a purely inseparable extension of a field `k`.
1. If a group `H` over `k` becomes isomorphic over `k'` to the diagonalizable group `D_{k'}(Λ)`
   of a finitely generated abelian group `Λ`, then `H` is isomorphic over `k` to `D_k(Λ')` for
   some finitely generated abelian group `Λ'`.
2. For groups `G`, `H` of multiplicative type over `k`, base change along `k → k'` is a
   bijection from the homomorphisms `G ⟶ H` onto the homomorphisms `G_{k'} ⟶ H_{k'}`. -/
def MultiplicativeTypePurelyInseparableStatement : Prop :=
  ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'], IsPurelyInseparable k k' →
    (∀ (H : GroupScheme (Spec (CommRingCat.of k)))
        (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ],
        Nonempty (((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj H) ≅
            (Diagonalizable.groupScheme (CommRingCat.of k') Λ).toGrp) →
        ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
          Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp)) ∧
    (∀ G H : GroupScheme (Spec (CommRingCat.of k)),
        IsMultiplicativeType G → IsMultiplicativeType H →
        Function.Bijective (fun f : G ⟶ H =>
          (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).map f))

end Langlands.GroupScheme
